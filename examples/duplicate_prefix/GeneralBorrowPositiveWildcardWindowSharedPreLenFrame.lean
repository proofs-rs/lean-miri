import duplicate_prefix.GeneralBorrowPositiveWildcardWindowFunctionToShared
import duplicate_prefix.GeneralBorrowForestSharedPreLenFrame
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowSharedPreLenFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows

/-- The positive wildcard entry installs the same physical source/count/local
shape used by the concrete shared-length continuation. This changes no memory
or ownership assertion. -/
theorem ready (frame : CompilerFrameContext.ActualFrame) (value : Immediate Provenance)
    (count : UInt64) (borrowFrame : FrameState)
    (h : GeneralBorrowPositiveWildcardWindowFunctionToShared.Ready frame value count borrowFrame) :
    GeneralBorrowForestFunctionEntryToShared.Ready frame value count borrowFrame :=
  ⟨h.body,h.identity,h.callee,h.size,h.location,h.source,h.countSlot,h.lenSlot,h.exprSlot,
    h.noClocks,h.borrowed,h.immediate,h.slot0,h.slot7,h.slot8,h.slot10,h.slot13,h.slot9,h.slot15,h.slot16⟩

/-- All physical local facts needed immediately before the real slice-length
helper follow from the wildcard entry boundary and actual shared-expression
write shape. The ownership and expression step are handled separately. -/
theorem build (before : CompilerFrameContext.ActualFrame) (original value : Immediate Provenance)
    (count : UInt64) (borrowFrame : FrameState)
    (h : GeneralBorrowPositiveWildcardWindowFunctionToShared.Ready before original count borrowFrame)
    (valid : 12 < before.locals.size) :
    GeneralBorrowForestSharedPreLenFrame.Facts before
      (GeneralBorrowForestSharedPreLenFrame.after before valid value) count value :=
  GeneralBorrowForestSharedPreLenFrame.build before original value count borrowFrame
    (ready before original count borrowFrame h) valid
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowSharedPreLenFrame
