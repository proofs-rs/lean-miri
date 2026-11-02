import duplicate_prefix.S02SeparateDestinationExact
import duplicate_prefix.S02SeparateDestinationTransport

namespace DuplicatePrefix.S02SeparateDestinationSourceLive
open Miri Miri.Input Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- A distinct destination's real retag and uninitializing write retain the
source allocation's live row in the exact machine state. -/
theorem source_live_after_protect
    (current : Before) (place : MPlaceTy Provenance)
    (destination : DuplicatePrefixReturnPlaceInput.Input current place)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (fresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (sourceId : AllocId) (different : destination.id ≠ sourceId) :
    (S04ProtectUninit.finished current place destination frames frame borrowFrame fresh tree updated).machine.memory.live.find?
      (fun row => row.1 == sourceId) =
    current.memory.live.find? (fun row => row.1 == sourceId) := by
  have first := S02SeparateDestinationTransport.other_live current.memory destination.id sourceId
    destination.entry tree different
  have second : (((RetagEntry.updatedMemory current.memory destination.id destination.entry tree).live.filter
      (fun row => row.1 != destination.id)).push
      (destination.id,{destination.entry with allocation := updated})).find?
      (fun row => row.1 == sourceId) =
      (RetagEntry.updatedMemory current.memory destination.id destination.entry tree).live.find?
        (fun row => row.1 == sourceId) := by
    simp only [Array.find?_push, Array.find?_filter]
    simp only [show (destination.id == sourceId) = false from by simp [different],
      Bool.false_eq_true,↓reduceIte,Option.or_none]
    congr 1
    funext row
    by_cases same : row.1 = sourceId
    · simp [same, Ne.symm different]
    · simp [same]
  change (((RetagEntry.updatedMemory current.memory destination.id destination.entry tree).live.filter
      (fun row => row.1 != destination.id)).push
      (destination.id,{destination.entry with allocation := updated})).find?
      (fun row => row.1 == sourceId) = _
  exact second.trans first

end
end DuplicatePrefix.S02SeparateDestinationSourceLive

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationSourceLive.source_live_after_protect) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination source-live dependency {dependency}"
