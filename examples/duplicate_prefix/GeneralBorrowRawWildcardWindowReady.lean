import duplicate_prefix.GeneralBorrowRawWildcardWindowFunctionToShared
import duplicate_prefix.GeneralBorrowRawWildcardFunctionToShared
namespace DuplicatePrefix.GeneralBorrowRawWildcardWindowReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
/-- Reuse the existing machine boundary API; all fields concern the current
frame/value rather than the allocation-relative source offset. -/
theorem to_base {frame : CompilerFrameContext.ActualFrame} {value : Immediate Provenance}
    {count : UInt64} {borrowFrame : FrameState}
    (ready : GeneralBorrowRawWildcardWindowFunctionToShared.Ready frame value count borrowFrame) :
    GeneralBorrowRawWildcardFunctionToShared.Ready frame value count borrowFrame := by
  cases ready
  constructor <;> assumption
end DuplicatePrefix.GeneralBorrowRawWildcardWindowReady
