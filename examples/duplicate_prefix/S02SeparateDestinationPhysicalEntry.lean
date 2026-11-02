import duplicate_prefix.S02SeparateDestinationPhysicalIdentity
import duplicate_prefix.S04ProtectUninit

namespace DuplicatePrefix.S02SeparateDestinationPhysicalEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- On the exact uninit state, the independently reconstructed physical
Destination points to the actual updated allocation row. -/
theorem updated_row {before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance}
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (physical : S03FinalReturnInputBounds.Destination
      (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated).machine place)
    (returnTag : BorTag) (concrete : input.pointer.provenance = .concrete input.id returnTag) :
    physical.entry = {input.entry with allocation := updated} := by
  have ids := S02SeparateDestinationPhysicalIdentity.original input physical returnTag concrete
  have live : (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated).machine.memory.live.find?
      (fun row => row.1 == input.id) = some (input.id,{input.entry with allocation := updated}) :=
    MemoryCopyBridge.live_lookup_replaced
      (ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree).machine.memory
      input.id {input.entry with allocation := updated}
  have physicalLive : (S04ProtectUninit.finished before place input frames frame borrowFrame fresh tree updated).machine.memory.live.find?
      (fun row => row.1 == input.id) = some (input.id,physical.entry) := by
    simpa only [ids.1] using physical.live
  exact congrArg Prod.snd (Option.some.inj (physicalLive.symm.trans live))

end DuplicatePrefix.S02SeparateDestinationPhysicalEntry

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationPhysicalEntry.updated_row) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination physical-entry dependency {dependency}"
