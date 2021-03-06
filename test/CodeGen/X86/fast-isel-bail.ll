; RUN: llvm-as < %s | llc -march=x86 -fast

; This file is for regression tests for cases where FastISel needs
; to gracefully bail out and let SelectionDAGISel take over.

	type { i64, i8* }		; type %0

declare void @bar(%0)

define fastcc void @foo() nounwind {
entry:
	call void @bar(%0 zeroinitializer)
	unreachable
}
