import Miri.Interpreter.ReallocationDriver

open Miri.ABI Miri.Memory Miri.Interpreter Miri.Memory.AllocAddresses
open Miri.TreeBorrows

private structure User where
  registry : MemoryExtras.Registry Unit := {}

private abbrev Wrapped := PointerMachine.User User
private abbrev State := PointerMachine.State Unit User

private def extras : MemoryExtras.Hooks Unit Wrapped Unit where
  get := fun user => user.payload.registry
  put := fun user registry => {user with payload := {user.payload with registry}}
  onAccess := fun _ _ => pure ()
  weakError := fun _ => .invalidProgram "unexpected weak error"

private def initial : State :=
  ⟨Stack.empty, {
    memory := MemoryState.empty
    borrowTracker := none
    dataRace := none
    threads := Miri.Concurrency.ThreadManager.initial false
    raceAllocations := #[]
    allocationSpans := #[]
    user := {
      addresses := {provenanceMode := .default, addressMode := .managed, generation := none}
      payload := {} } }⟩

private def configured : PlaceMachine.AllocationConfig Unit Wrapped where
  maximumObjectSize := Size.ofBytes 64
  zeroedStorage := fun size _ => some (Array.replicate size.bytes.toNat 0)
  diagnostic := fun _ _ _ => pure ()
  allocationTail := fun id _ _ => MemoryExtras.initAllocation extras id false
  adjustRootAddress := fun id tag => pure (Pointer.new (.concrete id tag) Size.ZERO)

private def wrapped : ReallocationDriver.CreationHooks Unit User Unit where
  extras
  allocation := configured
  weakMemory := false
  globalKind := none

def main : IO Unit := do
  let size := Size.ofBytes 4
  let old := (ReallocationDriver.allocateSourceFrom wrapped size Align.ONE (.machine ()) .Uninit).run initial
  match old with
  | .ok _ _ => throw (IO.userError "doubly bound extras unexpectedly succeeded")
  | .error error _ =>
    if error != .invalidProgram "allocation extras initialized twice" then
      throw (IO.userError s!"unexpected old path failure: {reprStr error}")
  let fixed := (ReallocationDriver.allocateConfigured configured size Align.ONE (.machine ()) .Uninit).run initial
  match fixed with
  | .error error _ => throw (IO.userError s!"configured allocation failed: {reprStr error}")
  | .ok pointer state =>
    let some id := PointerProvenance.getAllocId pointer.provenance
      | throw (IO.userError "configured root lacks allocation provenance")
    if state.machine.memory.live.size != 1 ||
        state.machine.user.payload.registry.allocations.map Prod.fst != #[id] then
      throw (IO.userError "configured allocation lost the single extras owner")
  IO.println "Configured allocation extras: reproduced duplicate and verified one owner"
