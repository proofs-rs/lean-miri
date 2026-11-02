import duplicate_prefix.GeneralBorrowForestAsMutDefaultCore
namespace DuplicatePrefix.GeneralBorrowForestAsMutDefaultFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- Lazy destination caching commutes with writing the distinct mutable
argument local. Both orders retain the exact source frame and MIR location. -/
theorem cache_write (frame : CompilerFrameContext.ActualFrame)
    (dest argument : MIR.LocalId) (different : argument ≠ dest)
    (validDest : dest < frame.locals.size) (validArgument : argument < frame.locals.size)
    (destLayout argumentLayout : LocalLayout) (value : Immediate Provenance) (location : Location) :
    LocalPlaces.cachePlaceLayout
      (CopyHelperSteps.advance (ActualLocalCopy.written frame argument argumentLayout validArgument value) location)
      dest destLayout (by simpa [CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using validDest) =
    CopyHelperSteps.advance
      (ActualLocalCopy.written (LocalPlaces.cachePlaceLayout frame dest destLayout validDest)
        argument argumentLayout (by simpa [LocalPlaces.cachePlaceLayout] using validArgument) value) location := by
  simp only [CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.getElem_set_self,
    Array.getElem_set,Array.set_set,if_neg different,if_neg (Ne.symm different)]
  congr 1
  exact Array.set_comm _ _ different

/-- An immediate local write and its cache preserve the absence of indirect
operands required by the later concrete frame cleanup. -/
theorem all_immediate (frame : CompilerFrameContext.ActualFrame) (id : MIR.LocalId)
    (layout : LocalLayout) (valid : id < frame.locals.size) (value : Immediate Provenance)
    (all : CopyHelperCleanup.AllImmediate frame) :
    CopyHelperCleanup.AllImmediate (ActualLocalCopy.written frame id layout valid value) := by
  have cached : CopyHelperCleanup.AllImmediate (LocalPlaces.cachePlaceLayout frame id layout valid) := by
    apply CopyHelperCleanup.all_immediate_set frame id {frame.locals[id] with layout := some layout} valid all
    intro memory
    exact all frame.locals[id] (Array.getElem_mem valid) memory
  exact CopyHelperCleanup.all_immediate_set _ id _ _ cached (fun _ => by simp)
end DuplicatePrefix.GeneralBorrowForestAsMutDefaultFrame
