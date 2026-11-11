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

private def access : PlaceMachine.AccessConfig Unit Wrapped where
  runtime := {RuntimeTargetDataLayout.default with base := ⟨.little,.w64⟩}
  ghostMode := false
  globalKind := none
  globalHooks := {
    synchronizeMemory := fun _ state => state
    evaluateStaticInitializer := fun memory state _ => ⟨memory,state,.error "unexpected global"⟩
    beforeAccessGlobal := fun memory state _ _ _ _ => ⟨memory,state,.error "unexpected global"⟩
    adjustGlobalAllocation := fun memory state _ _ => ⟨memory,state,.error "unexpected global"⟩ }
  dynamicLayout := fun memory state _ => ⟨memory,state,.ok none⟩
  resolvePointer := fun _ pointer _ machine => match pointer.provenance with
    | some (.concrete id tag) => .ok (.ok ⟨id,pointer.offset,.concrete tag⟩) machine
    | _ => .ok (.error pointer.offset.bytes) machine
  beforeAllocationAccess := fun _ => pure ()
  diagnostic := fun write _ _ => event (if write then "write" else "read")
  weakMemoryWrite := fun _ _ => pure ()
  syncAccess := fun _ _ _ => pure ()
  retainTouched := fun machine _ => machine
  memoryError := fun error => .invalidProgram (reprStr error)

private def allocationAt (state : State) (id : AllocId) : IO (Allocation Provenance BorrowTree) := do
  let some (_,entry) := state.machine.memory.live.find? (·.1 == id)
    | throw (IO.userError "expected allocation disappeared")
  pure entry.allocation

private def pointerId (pointer : Pointer Provenance) : IO AllocId := do
  let some id := PointerProvenance.getAllocId pointer.provenance
    | throw (IO.userError "configured pointer lacks allocation identity")
  pure id

/-- Real lifecycle removal, including its remove-before-hook failure prefix. -/
private def destroy (fail : Bool) (pointer : Pointer (Option Provenance))
    (layout : Option (Size × Align)) (kind : MemoryKind Unit) : PointerMachine.M Unit User Unit := do
  let state ← get
  let hooks : MemoryDeallocationHooks Provenance BorrowTree Unit
      (MachineHooks.MachineState Unit Wrapped) ProvenanceExtra := {
    synchronizeMemory := fun memory machine => {machine with memory}
    resolvePointer := fun memory machine pointer _ => match pointer.provenance with
      | some (.concrete id tag) => ⟨memory,machine,.ok ⟨id,pointer.offset,.concrete tag⟩⟩
      | _ => ⟨memory,machine,.error pointer.offset.bytes⟩
    beforeDeallocation := fun memory machine _ _ id _ _ _ _ =>
      let machine := {machine with user := {machine.user with payload :=
        {machine.user.payload with events := machine.user.payload.events.push "free"}}}
      if fail then ⟨memory,machine,.error "free rejected"⟩
      else match (MemoryExtras.removeAllocation extras id).run machine with
        | .ok () machine => ⟨memory,machine,.ok ()⟩
        | .error error machine => ⟨memory,machine,.error (reprStr error)⟩ }
  let result := MemoryLifecycle.deallocatePtrWith state.machine.memory state.machine pointer layout kind hooks
  set {state with machine := {result.hooks with memory := result.memory}}
  match result.outcome with
    | .ok () => pure ()
    | .error error => throw (.invalidProgram (reprStr error))

private def configuredReallocationChecks : IO Unit := do
  let align : Align := ⟨3⟩
  let setup := do
    let source ← ReallocationDriver.allocateConfigured collecting (Size.ofBytes 16) align (.machine ()) .Uninit
    let zero ← ReallocationDriver.allocateConfigured collecting (Size.ofBytes 8) align (.machine ()) .Zero
    pure (source,zero)
  let ((source,zero),state) ← match setup.run initial with
    | .ok pointers state => pure (pointers,state)
    | .error error _ => throw (IO.userError s!"aligned setup failed: {reprStr error}")
  let sourceId ← pointerId source
  let zeroId ← pointerId zero
  let sourceAllocation ← allocationAt state sourceId
  let zeroAllocation ← allocationAt state zeroId
  unless sourceId != zeroId && sourceAllocation.align == align && zeroAllocation.align == align &&
      sourceAllocation.initializationMask.get Size.ZERO == .ok false &&
      zeroAllocation.initializationMask.isRangeInitialized (allocRange Size.ZERO (Size.ofBytes 8)) == .ok (.ok ()) &&
      zeroAllocation.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 8)) == .ok (Array.replicate 8 0) do
    throw (IO.userError "aligned zero/uninitialized allocation contract changed")
  match (MemoryExtras.initAllocation extras sourceId false).run state.machine with
    | .ok _ _ => throw (IO.userError "already initialized identity was accepted")
    | .error error stopped =>
      unless error == .invalidProgram "allocation extras initialized twice" &&
          stopped.user.payload.registry.allocations.map Prod.fst == #[sourceId,zeroId] do
        throw (IO.userError "duplicate guard mutated ownership or changed error")
  let scalar := Scalar.fromPointer access.runtime.base zero
  let initialized ← match (Allocation.writeScalar access.runtime.base
      (allocRange Size.ZERO (Size.ofBytes 8)) scalar).run sourceAllocation with
    | .ok () allocation => pure allocation
    | .error error _ => throw (IO.userError s!"source pointer setup failed: {reprStr error}")
  let state := {state with machine := {state.machine with
    memory := {state.machine.memory with live := state.machine.memory.live.map fun (id,entry) =>
      (id,if id == sourceId then {entry with allocation := initialized} else entry)}
    user := {state.machine.user with payload := {state.machine.user.payload with events := #[]}}}}
  let runRealloc := fun access fail init =>
    ReallocationDriver.reallocateConfiguredFrom access extras ⟨Size.ofBytes 8⟩ collecting (destroy fail)
      source.withOptionalProvenance (some (Size.ofBytes 16,align)) (Size.ofBytes 24) align (.machine ()) init
  for init in #[AllocInit.Uninit,AllocInit.Zero] do
    let (dest,stopped) ← match (runRealloc access false init).run state with
      | .ok pointer stopped => pure (pointer,stopped)
      | .error error _ => throw (IO.userError s!"configured realloc failed: {reprStr error}")
    let destId ← pointerId dest
    let allocation ← allocationAt stopped destId
    unless destId != sourceId && destId != zeroId && allocation.align == align &&
        allocation.readScalar access.runtime.base (allocRange Size.ZERO (Size.ofBytes 8)) true == .ok scalar &&
        allocation.initializationMask.get (Size.ofBytes 8) == .ok false &&
        allocation.initializationMask.get (Size.ofBytes 16) == .ok (init == .Zero) &&
        stopped.machine.memory.live.map Prod.fst == #[zeroId,destId] &&
        stopped.machine.user.payload.registry.allocations.map Prod.fst == #[zeroId,destId] &&
        stopped.machine.user.payload.events == #["diagnostic","extras","capture","span","read","write","free"] do
      throw (IO.userError "realloc lost copy provenance/init mask/growth policy or allocate-copy-free ordering")
  let failingAccess := {access with diagnostic := fun write _ _ => do
    event (if write then "write" else "read")
    if !write then throw (.unsupported "copy rejected")}
  for (config,fail,expectedEvents) in #[(failingAccess,false,
      #["diagnostic","extras","capture","span","read"]),
      (access,true,#["diagnostic","extras","capture","span","read","write","free"])] do
    match (runRealloc config fail .Zero).run state with
    | .ok _ _ => throw (IO.userError "failing realloc unexpectedly succeeded")
    | .error _ stopped =>
      let ids := stopped.machine.user.payload.registry.allocations.map Prod.fst
      unless ids.size == 3 && ids[0]? == some sourceId && ids[1]? == some zeroId &&
          stopped.machine.memory.live.size == (if fail then 2 else 3) &&
          stopped.machine.user.payload.events == expectedEvents do
        throw (IO.userError "failed copy/free lost the new owner or source-ordered partial state")
      let some destId := ids[2]? | throw (IO.userError "failed realloc lost destination identity")
      let allocation ← allocationAt stopped destId
      unless allocation.initializationMask.get (Size.ofBytes 16) == .ok true &&
          (if fail then allocation.readScalar access.runtime.base
            (allocRange Size.ZERO (Size.ofBytes 8)) true == .ok scalar
           else allocation.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 8)) == .ok (Array.replicate 8 0)) do
        throw (IO.userError "failed realloc did not retain the actual copied/uncopied destination")

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
  configuredReallocationChecks
  IO.println "Configured allocation extras: one owner, aligned initialization, provenance-preserving realloc, failure prefixes and traces verified"
