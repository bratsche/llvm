//===- FunctionAttrs.cpp - Pass which marks functions readnone or readonly ===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements a simple interprocedural pass which walks the
// call-graph, looking for functions which do not access or only read
// non-local memory, and marking them readnone/readonly.  In addition,
// it marks function arguments (of pointer type) 'nocapture' if a call
// to the function does not create any copies of the pointer value that
// outlive the call.  This more or less means that the pointer is only
// dereferenced, and not returned from the function or stored in a global.
// This pass is implemented as a bottom-up traversal of the call-graph.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "functionattrs"
#include "llvm/Transforms/IPO.h"
#include "llvm/CallGraphSCCPass.h"
#include "llvm/GlobalVariable.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CaptureTracking.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/UniqueVector.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/InstIterator.h"
using namespace llvm;

STATISTIC(NumReadNone, "Number of functions marked readnone");
STATISTIC(NumReadOnly, "Number of functions marked readonly");
STATISTIC(NumNoCapture, "Number of arguments marked nocapture");
STATISTIC(NumNoAlias, "Number of function returns marked noalias");

namespace {
  struct VISIBILITY_HIDDEN FunctionAttrs : public CallGraphSCCPass {
    static char ID; // Pass identification, replacement for typeid
    FunctionAttrs() : CallGraphSCCPass(&ID) {}

    // runOnSCC - Analyze the SCC, performing the transformation if possible.
    bool runOnSCC(const std::vector<CallGraphNode *> &SCC);

    // AddReadAttrs - Deduce readonly/readnone attributes for the SCC.
    bool AddReadAttrs(const std::vector<CallGraphNode *> &SCC);

    // AddNoCaptureAttrs - Deduce nocapture attributes for the SCC.
    bool AddNoCaptureAttrs(const std::vector<CallGraphNode *> &SCC);

    // IsFunctionMallocLike - Does this function allocate new memory?
    bool IsFunctionMallocLike(Function *F,
                              SmallPtrSet<CallGraphNode*, 8> &) const;

    // AddNoAliasAttrs - Deduce noalias attributes for the SCC.
    bool AddNoAliasAttrs(const std::vector<CallGraphNode *> &SCC);

    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesCFG();
      CallGraphSCCPass::getAnalysisUsage(AU);
    }

    bool PointsToLocalMemory(Value *V);
  };
}

char FunctionAttrs::ID = 0;
static RegisterPass<FunctionAttrs>
X("functionattrs", "Deduce function attributes");

Pass *llvm::createFunctionAttrsPass() { return new FunctionAttrs(); }


/// PointsToLocalMemory - Returns whether the given pointer value points to
/// memory that is local to the function.  Global constants are considered
/// local to all functions.
bool FunctionAttrs::PointsToLocalMemory(Value *V) {
  V = V->getUnderlyingObject();
  // An alloca instruction defines local memory.
  if (isa<AllocaInst>(V))
    return true;
  // A global constant counts as local memory for our purposes.
  if (GlobalVariable *GV = dyn_cast<GlobalVariable>(V))
    return GV->isConstant();
  // Could look through phi nodes and selects here, but it doesn't seem
  // to be useful in practice.
  return false;
}

/// AddReadAttrs - Deduce readonly/readnone attributes for the SCC.
bool FunctionAttrs::AddReadAttrs(const std::vector<CallGraphNode *> &SCC) {
  SmallPtrSet<CallGraphNode*, 8> SCCNodes;
  CallGraph &CG = getAnalysis<CallGraph>();

  // Fill SCCNodes with the elements of the SCC.  Used for quickly
  // looking up whether a given CallGraphNode is in this SCC.
  for (unsigned i = 0, e = SCC.size(); i != e; ++i)
    SCCNodes.insert(SCC[i]);

  // Check if any of the functions in the SCC read or write memory.  If they
  // write memory then they can't be marked readnone or readonly.
  bool ReadsMemory = false;
  for (unsigned i = 0, e = SCC.size(); i != e; ++i) {
    Function *F = SCC[i]->getFunction();

    if (F == 0)
      // External node - may write memory.  Just give up.
      return false;

    if (F->doesNotAccessMemory())
      // Already perfect!
      continue;

    // Definitions with weak linkage may be overridden at linktime with
    // something that writes memory, so treat them like declarations.
    if (F->isDeclaration() || F->mayBeOverridden()) {
      if (!F->onlyReadsMemory())
        // May write memory.  Just give up.
        return false;

      ReadsMemory = true;
      continue;
    }

    // Scan the function body for instructions that may read or write memory.
    for (inst_iterator II = inst_begin(F), E = inst_end(F); II != E; ++II) {
      Instruction *I = &*II;

      // Some instructions can be ignored even if they read or write memory.
      // Detect these now, skipping to the next instruction if one is found.
      CallSite CS = CallSite::get(I);
      if (CS.getInstruction()) {
        // Ignore calls to functions in the same SCC.
        if (SCCNodes.count(CG[CS.getCalledFunction()]))
          continue;
      } else if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
        // Ignore loads from local memory.
        if (PointsToLocalMemory(LI->getPointerOperand()))
          continue;
      } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
        // Ignore stores to local memory.
        if (PointsToLocalMemory(SI->getPointerOperand()))
          continue;
      }

      // Any remaining instructions need to be taken seriously!  Check if they
      // read or write memory.
      if (I->mayWriteToMemory())
        // Writes memory.  Just give up.
        return false;
      // If this instruction may read memory, remember that.
      ReadsMemory |= I->mayReadFromMemory();
    }
  }

  // Success!  Functions in this SCC do not access memory, or only read memory.
  // Give them the appropriate attribute.
  bool MadeChange = false;
  for (unsigned i = 0, e = SCC.size(); i != e; ++i) {
    Function *F = SCC[i]->getFunction();

    if (F->doesNotAccessMemory())
      // Already perfect!
      continue;

    if (F->onlyReadsMemory() && ReadsMemory)
      // No change.
      continue;

    MadeChange = true;

    // Clear out any existing attributes.
    F->removeAttribute(~0, Attribute::ReadOnly | Attribute::ReadNone);

    // Add in the new attribute.
    F->addAttribute(~0, ReadsMemory? Attribute::ReadOnly : Attribute::ReadNone);

    if (ReadsMemory)
      ++NumReadOnly;
    else
      ++NumReadNone;
  }

  return MadeChange;
}

/// AddNoCaptureAttrs - Deduce nocapture attributes for the SCC.
bool FunctionAttrs::AddNoCaptureAttrs(const std::vector<CallGraphNode *> &SCC) {
  bool Changed = false;

  // Check each function in turn, determining which pointer arguments are not
  // captured.
  for (unsigned i = 0, e = SCC.size(); i != e; ++i) {
    Function *F = SCC[i]->getFunction();

    if (F == 0)
      // External node - skip it;
      continue;

    // Definitions with weak linkage may be overridden at linktime with
    // something that writes memory, so treat them like declarations.
    if (F->isDeclaration() || F->mayBeOverridden())
      continue;

    for (Function::arg_iterator A = F->arg_begin(), E = F->arg_end(); A!=E; ++A)
      if (isa<PointerType>(A->getType()) && !A->hasNoCaptureAttr() &&
          !PointerMayBeCaptured(A, true)) {
        A->addAttr(Attribute::NoCapture);
        ++NumNoCapture;
        Changed = true;
      }
  }

  return Changed;
}

/// IsFunctionMallocLike - A function is malloc-like if it returns either null
/// or a pointer that doesn't alias any other pointer visible to the caller.
bool FunctionAttrs::IsFunctionMallocLike(Function *F,
                              SmallPtrSet<CallGraphNode*, 8> &SCCNodes) const {
  CallGraph &CG = getAnalysis<CallGraph>();

  UniqueVector<Value *> FlowsToReturn;
  for (Function::iterator I = F->begin(), E = F->end(); I != E; ++I)
    if (ReturnInst *Ret = dyn_cast<ReturnInst>(I->getTerminator()))
      FlowsToReturn.insert(Ret->getReturnValue());

  for (unsigned i = 0; i != FlowsToReturn.size(); ++i) {
    Value *RetVal = FlowsToReturn[i+1];   // UniqueVector[0] is reserved.

    if (Constant *C = dyn_cast<Constant>(RetVal)) {
      if (!C->isNullValue() && !isa<UndefValue>(C))
        return false;

      continue;
    }

    if (isa<Argument>(RetVal))
      return false;

    if (Instruction *RVI = dyn_cast<Instruction>(RetVal))
      switch (RVI->getOpcode()) {
        // Extend the analysis by looking upwards.
        case Instruction::GetElementPtr:
        case Instruction::BitCast:
          FlowsToReturn.insert(RVI->getOperand(0));
          continue;
        case Instruction::Select: {
          SelectInst *SI = cast<SelectInst>(RVI);
          FlowsToReturn.insert(SI->getTrueValue());
          FlowsToReturn.insert(SI->getFalseValue());
        } continue;
        case Instruction::PHI: {
          PHINode *PN = cast<PHINode>(RVI);
          for (int i = 0, e = PN->getNumIncomingValues(); i != e; ++i)
            FlowsToReturn.insert(PN->getIncomingValue(i));
        } continue;

        // Check whether the pointer came from an allocation.
        case Instruction::Alloca:
        case Instruction::Malloc:
          break;
        case Instruction::Call:
        case Instruction::Invoke: {
          CallSite CS(RVI);
          if (CS.paramHasAttr(0, Attribute::NoAlias))
            break;
          if (CS.getCalledFunction() &&
              SCCNodes.count(CG[CS.getCalledFunction()]))
            break;
        } // fall-through
        default:
          return false;  // Did not come from an allocation.
      }

    if (PointerMayBeCaptured(RetVal, false))
      return false;
  }

  return true;
}

/// AddNoAliasAttrs - Deduce noalias attributes for the SCC.
bool FunctionAttrs::AddNoAliasAttrs(const std::vector<CallGraphNode *> &SCC) {
  SmallPtrSet<CallGraphNode*, 8> SCCNodes;

  // Fill SCCNodes with the elements of the SCC.  Used for quickly
  // looking up whether a given CallGraphNode is in this SCC.
  for (unsigned i = 0, e = SCC.size(); i != e; ++i)
    SCCNodes.insert(SCC[i]);

  // Check each function in turn, determining which functions return noalias
  // pointers.
  for (unsigned i = 0, e = SCC.size(); i != e; ++i) {
    Function *F = SCC[i]->getFunction();

    if (F == 0)
      // External node - skip it;
      return false;

    // Already noalias.
    if (F->doesNotAlias(0))
      continue;

    // Definitions with weak linkage may be overridden at linktime, so
    // treat them like declarations.
    if (F->isDeclaration() || F->mayBeOverridden())
      return false;

    // We annotate noalias return values, which are only applicable to 
    // pointer types.
    if (!isa<PointerType>(F->getReturnType()))
      continue;

    if (!IsFunctionMallocLike(F, SCCNodes))
      return false;
  }

  bool MadeChange = false;
  for (unsigned i = 0, e = SCC.size(); i != e; ++i) {
    Function *F = SCC[i]->getFunction();
    if (F->doesNotAlias(0) || !isa<PointerType>(F->getReturnType()))
      continue;

    F->setDoesNotAlias(0);
    ++NumNoAlias;
    MadeChange = true;
  }

  return MadeChange;
}

bool FunctionAttrs::runOnSCC(const std::vector<CallGraphNode *> &SCC) {
  bool Changed = AddReadAttrs(SCC);
  Changed |= AddNoCaptureAttrs(SCC);
  Changed |= AddNoAliasAttrs(SCC);
  return Changed;
}
