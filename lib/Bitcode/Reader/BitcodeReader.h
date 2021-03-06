//===- BitcodeReader.h - Internal BitcodeReader impl ------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This header defines the BitcodeReader class.
//
//===----------------------------------------------------------------------===//

#ifndef BITCODE_READER_H
#define BITCODE_READER_H

#include "llvm/ModuleProvider.h"
#include "llvm/Attributes.h"
#include "llvm/Type.h"
#include "llvm/OperandTraits.h"
#include "llvm/Bitcode/BitstreamReader.h"
#include "llvm/Bitcode/LLVMBitCodes.h"
#include "llvm/Support/ValueHandle.h"
#include "llvm/ADT/DenseMap.h"
#include <vector>

namespace llvm {
  class MemoryBuffer;
  
//===----------------------------------------------------------------------===//
//                          BitcodeReaderValueList Class
//===----------------------------------------------------------------------===//

class BitcodeReaderValueList {
  std::vector<WeakVH> ValuePtrs;
  
  /// ResolveConstants - As we resolve forward-referenced constants, we add
  /// information about them to this vector.  This allows us to resolve them in
  /// bulk instead of resolving each reference at a time.  See the code in
  /// ResolveConstantForwardRefs for more information about this.
  ///
  /// The key of this vector is the placeholder constant, the value is the slot
  /// number that holds the resolved value.
  typedef std::vector<std::pair<Constant*, unsigned> > ResolveConstantsTy;
  ResolveConstantsTy ResolveConstants;
public:
  BitcodeReaderValueList() {}
  ~BitcodeReaderValueList() {
    assert(ResolveConstants.empty() && "Constants not resolved?");
  }

  // vector compatibility methods
  unsigned size() const { return ValuePtrs.size(); }
  void resize(unsigned N) { ValuePtrs.resize(N); }
  void push_back(Value *V) {
    ValuePtrs.push_back(V);
  }
  
  void clear() {
    assert(ResolveConstants.empty() && "Constants not resolved?");
    ValuePtrs.clear();
  }
  
  Value *operator[](unsigned i) const {
    assert(i < ValuePtrs.size());
    return ValuePtrs[i];
  }
  
  Value *back() const { return ValuePtrs.back(); }
    void pop_back() { ValuePtrs.pop_back(); }
  bool empty() const { return ValuePtrs.empty(); }
  void shrinkTo(unsigned N) {
    assert(N <= size() && "Invalid shrinkTo request!");
    ValuePtrs.resize(N);
  }
  
  Constant *getConstantFwdRef(unsigned Idx, const Type *Ty);
  Value *getValueFwdRef(unsigned Idx, const Type *Ty);
  
  void AssignValue(Value *V, unsigned Idx);
  
  /// ResolveConstantForwardRefs - Once all constants are read, this method bulk
  /// resolves any forward references.
  void ResolveConstantForwardRefs();
};

class BitcodeReader : public ModuleProvider {
  MemoryBuffer *Buffer;
  BitstreamReader Stream;
  
  const char *ErrorString;
  
  std::vector<PATypeHolder> TypeList;
  BitcodeReaderValueList ValueList;
  std::vector<std::pair<GlobalVariable*, unsigned> > GlobalInits;
  std::vector<std::pair<GlobalAlias*, unsigned> > AliasInits;
  
  /// MAttributes - The set of attributes by index.  Index zero in the
  /// file is for null, and is thus not represented here.  As such all indices
  /// are off by one.
  std::vector<AttrListPtr> MAttributes;
  
  /// FunctionBBs - While parsing a function body, this is a list of the basic
  /// blocks for the function.
  std::vector<BasicBlock*> FunctionBBs;
  
  // When reading the module header, this list is populated with functions that
  // have bodies later in the file.
  std::vector<Function*> FunctionsWithBodies;

  // When intrinsic functions are encountered which require upgrading they are 
  // stored here with their replacement function.
  typedef std::vector<std::pair<Function*, Function*> > UpgradedIntrinsicMap;
  UpgradedIntrinsicMap UpgradedIntrinsics;
  
  // After the module header has been read, the FunctionsWithBodies list is 
  // reversed.  This keeps track of whether we've done this yet.
  bool HasReversedFunctionsWithBodies;
  
  /// DeferredFunctionInfo - When function bodies are initially scanned, this
  /// map contains info about where to find deferred function body (in the
  /// stream) and what linkage the original function had.
  DenseMap<Function*, std::pair<uint64_t, unsigned> > DeferredFunctionInfo;
public:
  explicit BitcodeReader(MemoryBuffer *buffer)
      : Buffer(buffer), ErrorString(0) {
    HasReversedFunctionsWithBodies = false;
  }
  ~BitcodeReader() {
    FreeState();
  }
  
  void FreeState();
  
  /// releaseMemoryBuffer - This causes the reader to completely forget about
  /// the memory buffer it contains, which prevents the buffer from being
  /// destroyed when it is deleted.
  void releaseMemoryBuffer() {
    Buffer = 0;
  }
  
  virtual bool materializeFunction(Function *F, std::string *ErrInfo = 0);
  virtual Module *materializeModule(std::string *ErrInfo = 0);
  virtual void dematerializeFunction(Function *F);
  virtual Module *releaseModule(std::string *ErrInfo = 0);

  bool Error(const char *Str) {
    ErrorString = Str;
    return true;
  }
  const char *getErrorString() const { return ErrorString; }
  
  /// @brief Main interface to parsing a bitcode buffer.
  /// @returns true if an error occurred.
  bool ParseBitcode();
private:
  const Type *getTypeByID(unsigned ID, bool isTypeTable = false);
  Value *getFnValueByID(unsigned ID, const Type *Ty) {
    return ValueList.getValueFwdRef(ID, Ty);
  }
  BasicBlock *getBasicBlock(unsigned ID) const {
    if (ID >= FunctionBBs.size()) return 0; // Invalid ID
    return FunctionBBs[ID];
  }
  AttrListPtr getAttributes(unsigned i) const {
    if (i-1 < MAttributes.size())
      return MAttributes[i-1];
    return AttrListPtr();
  }
  
  /// getValueTypePair - Read a value/type pair out of the specified record from
  /// slot 'Slot'.  Increment Slot past the number of slots used in the record.
  /// Return true on failure.
  bool getValueTypePair(SmallVector<uint64_t, 64> &Record, unsigned &Slot,
                        unsigned InstNum, Value *&ResVal) {
    if (Slot == Record.size()) return true;
    unsigned ValNo = (unsigned)Record[Slot++];
    if (ValNo < InstNum) {
      // If this is not a forward reference, just return the value we already
      // have.
      ResVal = getFnValueByID(ValNo, 0);
      return ResVal == 0;
    } else if (Slot == Record.size()) {
      return true;
    }
    
    unsigned TypeNo = (unsigned)Record[Slot++];
    ResVal = getFnValueByID(ValNo, getTypeByID(TypeNo));
    return ResVal == 0;
  }
  bool getValue(SmallVector<uint64_t, 64> &Record, unsigned &Slot,
                const Type *Ty, Value *&ResVal) {
    if (Slot == Record.size()) return true;
    unsigned ValNo = (unsigned)Record[Slot++];
    ResVal = getFnValueByID(ValNo, Ty);
    return ResVal == 0;
  }

  
  bool ParseModule(const std::string &ModuleID);
  bool ParseAttributeBlock();
  bool ParseTypeTable();
  bool ParseTypeSymbolTable();
  bool ParseValueSymbolTable();
  bool ParseConstants();
  bool RememberAndSkipFunctionBody();
  bool ParseFunctionBody(Function *F);
  bool ResolveGlobalAndAliasInits();
};
  
} // End llvm namespace

#endif
