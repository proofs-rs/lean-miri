import Miri.Interpreter.ReallocationDriver

open Miri.ABI Miri.Memory Miri.Interpreter Miri.Memory.AllocAddresses
open Miri.TreeBorrows

private structure User where
  registry : MemoryExtras.Registry Unit := {}
  events : Array String := #[]

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

private def event (name : String) : PlaceMachine.MachineM Unit Wrapped Unit :=
  modify fun machine => {machine with user := {machine.user with payload :=
    {machine.user.payload with events := machine.user.payload.events.push name}}}

private def collecting : PlaceMachine.AllocationConfig Unit Wrapped :=
  {configured with
    discardUninserted := fun id => modify (fun machine => MemoryExtras.discardUninserted extras id machine)
    diagnostic := fun _ _ _ => event "diagnostic"
    allocationTail := fun id _ _ => do
      MemoryExtras.initAllocation extras id false
      event "extras"
    allocationBacktrace := some (fun id _ => do
      let state ← get
      if state.machine.memory.live.any (·.1 == id) then
        throw (.invalidProgram "backtrace capture ran after live insertion")
      let extra ← match MemoryExtras.lookup extras state.machine id with
        | .ok extra => pure extra | .error error => throw error
      if extra.backtrace.isSome then throw (.invalidProgram "fresh allocation has old trace")
      let serial := state.machine.memory.live.size
      let trace := #[(serial, Miri.MIR.SpanRef.mk serial)]
      match (MemoryExtras.recordBacktrace extras id trace).run state.machine with
      | .error error machine => set {state with machine}; throw error
      | .ok () machine =>
        match (event "capture").run machine with
        | .error error machine => set {state with machine}; throw error
        | .ok () machine => set {state with machine})
    allocationSpan := fun id _ _ => do
      let machine ← get
      let extra ← match MemoryExtras.lookup extras machine id with
        | .ok extra => pure extra | .error error => throw error
      if extra.backtrace.isNone then throw (.invalidProgram "span saved before backtrace capture")
      event "span"}

private def backtraceChecks : IO Unit := do
  let action := do
    let first ← ReallocationDriver.allocateConfigured collecting (Size.ofBytes 4) Align.ONE (.machine ()) .Uninit
    let second ← ReallocationDriver.allocateConfigured collecting (Size.ofBytes 4) Align.ONE (.machine ()) .Uninit
    pure (first,second)
  let ((first,second),state) ← match action.run initial with
    | .ok pointers state => pure (pointers,state)
    | .error error _ => throw (IO.userError s!"backtrace allocation failed: {reprStr error}")
  let some firstId := PointerProvenance.getAllocId first.provenance
    | throw (IO.userError "first allocation lacks ID")
  let some secondId := PointerProvenance.getAllocId second.provenance
    | throw (IO.userError "second allocation lacks ID")
  unless firstId != secondId && state.machine.user.payload.events ==
      #["diagnostic","extras","capture","span","diagnostic","extras","capture","span"] do
    throw (IO.userError "allocation-time collection order or allocation identity changed")
  let registry := state.machine.user.payload.registry
  let firstTrace := (registry.allocations.find? (·.1 == firstId)).bind (·.2.backtrace)
  let secondTrace := (registry.allocations.find? (·.1 == secondId)).bind (·.2.backtrace)
  unless firstTrace == some #[(0,⟨0⟩)] && secondTrace == some #[(1,⟨1⟩)] do
    throw (IO.userError "per-allocation backtraces were overwritten by a later allocation")
  let removed ← match (MemoryExtras.removeAllocation extras firstId).run state.machine with
    | .ok () machine => pure machine
    | .error error _ => throw (IO.userError s!"trace removal failed: {reprStr error}")
  unless removed.user.payload.registry.allocations.map Prod.fst == #[secondId] &&
      ((removed.user.payload.registry.allocations[0]?).bind (·.2.backtrace)) == secondTrace do
    throw (IO.userError "trace removal lost an unrelated allocation's trace")
  -- Diagnostic/tree failures precede the new collection boundary. Their
  -- already performed mutations must retain the pre-existing API behavior.
  let diagnosticFailure := {collecting with
    allocationBacktrace := none
    diagnostic := fun id _ _ => do
      modify fun machine => {machine with allocationSpans := machine.allocationSpans.push (id,⟨0⟩,none)}
      throw (.unsupported "diagnostic failed")}
  match (ReallocationDriver.allocateConfigured diagnosticFailure (Size.ofBytes 4) Align.ONE (.machine ()) .Uninit).run initial with
  | .ok _ _ => throw (IO.userError "failing diagnostic succeeded")
  | .error error stopped =>
    unless error == .unsupported "diagnostic failed" && stopped.machine.allocationSpans.size == 1 do
      throw (IO.userError "pre-collection diagnostic failure lost its mutation prefix")
  let failing := {collecting with allocationSpan := fun _ _ _ => throw (.unsupported "span query failed")}
  match (ReallocationDriver.allocateConfigured failing (Size.ofBytes 4) Align.ONE (.machine ()) .Uninit).run state with
  | .ok _ _ => throw (IO.userError "failing source span query was counted as successful allocation")
  | .error error stopped =>
    unless error == .unsupported "span query failed" &&
        stopped.machine.user.payload.registry.allocations.map Prod.fst == #[firstId,secondId] &&
        stopped.machine.memory.live.map Prod.fst == #[firstId,secondId] do
      throw (IO.userError "failed initialization retained its trace or discarded another allocation")

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
  backtraceChecks
  IO.println "Configured allocation extras: one owner, allocation-time traces and cleanup verified"
