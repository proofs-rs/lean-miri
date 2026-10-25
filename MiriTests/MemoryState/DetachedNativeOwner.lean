import Miri.Interpreter.AllocationMachine

open Miri.ABI Miri.Memory Miri.Interpreter Miri.Interpreter.MemoryExtras
open Miri.TreeBorrows

private def targetId : AllocId := ⟨1, by decide⟩
private def resolverRemovedId : AllocId := ⟨2, by decide⟩
private def hookRemovedId : AllocId := ⟨3, by decide⟩
private def survivorId : AllocId := ⟨4, by decide⟩
private def tag : BorTag := ⟨1, by decide⟩

private def extraFor (id : AllocId) : AllocationExtra Unit := {
  weakMemory := none
  sync := if id == targetId || id == resolverRemovedId then
    #[⟨Size.ZERO, {payload := (), deleteOnWrite := id == resolverRemovedId, roots := #[]}⟩]
    else #[] }

private structure UserState where
  registry : Registry Unit
  events : Array String := #[]
  released : Array Nat := #[]
  failSync : Bool := false

private def allocation (owner : Nat) : IO (Allocation Provenance BorrowTree) := do
  let bytes ← match Allocation.fromBytes (Prov := Provenance) (Array.replicate 4 (0 : UInt8)) Align.ONE .Mut with
    | .ok value => pure value
    | .error error => throw (IO.userError (toString error))
  let tree := BorrowTree.new tag (Size.ofBytes 4)
  let bytes := bytes.withExtra tree
  match bytes.attachNativeBuffer ⟨owner,true,4,1⟩ with
  | .ok bytes => pure bytes
  | .error error => throw (IO.userError error)

private def machineState (failSync : Bool) : IO (MachineHooks.State Unit UserState) := do
  let getAlloc (id : AllocId) (owner : Nat) : IO (AllocId × LocalAllocation Provenance BorrowTree Unit) := do
    let bytes ← allocation owner
    pure (id, ⟨.machine (), bytes.setExtra (BorrowTree.new tag (Size.ofBytes 4))⟩)
  let values := #[
    (← getAlloc targetId 101),
    (← getAlloc resolverRemovedId 202),
    (← getAlloc hookRemovedId 303),
    (← getAlloc survivorId 404)]
  let issued := MemoryState.setIssuedIds
    (MemoryState.empty : MemoryState Provenance BorrowTree Unit)
    #[targetId,resolverRemovedId,hookRemovedId,survivorId]
  let memory : MemoryState Provenance BorrowTree Unit :=
    { issued with nextAllocId := 5, live := values }
  let registry : Registry Unit := { allocations := #[
    (targetId,extraFor targetId), (resolverRemovedId,extraFor resolverRemovedId),
    (hookRemovedId,extraFor hookRemovedId), (survivorId,extraFor survivorId)] }
  let clock := Miri.Concurrency.VClockAlloc.newAllocation
    (Miri.Concurrency.ByteSize.ofU64 4 (by decide))
    (match Miri.Concurrency.VTimestamp.ofTime 0 with | .ok value => value | .error _ => .ZERO)
    (.ofU32 0 (by decide))
  let machine : MachineHooks.MachineState Unit UserState := {
    memory
    borrowTracker := none
    dataRace := none
    threads := Miri.Concurrency.ThreadManager.initial false
    raceAllocations := #[(targetId,clock),(resolverRemovedId,clock),(hookRemovedId,clock),(survivorId,clock)]
    allocationSpans := #[]
    user := ⟨registry,#[],#[],failSync⟩ }
  return ⟨Stack.empty,machine⟩

private def extras : MemoryExtras.Hooks Unit UserState Unit where
  get := UserState.registry
  put := fun user registry => {user with registry}
  weakError := fun _ => .invalidProgram "unexpected weak-memory error"
  onAccess := fun _ kind => do
    let machine ← get
    let registry := machine.user.registry
    let hookEntry := (hookRemovedId, extraFor hookRemovedId)
    let registry := {registry with allocations :=
      (registry.allocations.filter (fun entry => entry.1 != hookRemovedId)).push hookEntry}
    let memory := {machine.memory with live := machine.memory.live.filter (fun entry => entry.1 != hookRemovedId)}
    let hookRace := machine.raceAllocations.find? (fun entry => entry.1 == hookRemovedId)
    let races := machine.raceAllocations.filter (fun entry => entry.1 != hookRemovedId)
    let races := match hookRace with | some entry => races.push entry | none => races
    let events := machine.user.events.push
      (if kind == .deallocation then
        if machine.user.failSync then "sync-failure" else "sync-success"
      else "unexpected-access")
    set {machine with
      memory
      raceAllocations := races
      user := {machine.user with registry, events}}
    if machine.user.failSync then throw (.callback "sync failure after detached removal")

private def hooks (failResolve : Bool) : AllocationMachine.DeallocationHooks Unit UserState Unit := {
  extras
  resolvePointer := fun memory access pointer _ =>
    let memory := {memory with live := memory.live.filter (fun entry => entry.1 != resolverRemovedId)}
    let machine := access.machine
    let registry := machine.user.registry
    let resolverEntry := (resolverRemovedId, extraFor resolverRemovedId)
    let registry := {registry with allocations :=
      (registry.allocations.filter (fun entry => entry.1 != resolverRemovedId)).push resolverEntry}
    let resolverRace := machine.raceAllocations.find? (fun entry => entry.1 == resolverRemovedId)
    let races := machine.raceAllocations.filter (fun entry => entry.1 != resolverRemovedId)
    let races := match resolverRace with | some entry => races.push entry | none => races
    let state := {access with machine := {machine with
      memory
      raceAllocations := races
      user := {machine.user with registry, events := machine.user.events.push "resolve"}}}
    if failResolve then ⟨memory,state,.error pointer.offset.bytes⟩
    else ⟨memory,state,.ok (targetId,pointer.offset,.concrete tag)⟩
  diagnostic := fun _ => pure ()
  currentSpan := pure ⟨0⟩
  freeAllocId := fun _ _ _ _ => pure ()
  retainDetached := fun _ machine => machine
  nativeDrop := some fun allocation => do
    let some owner := allocation.nativeBuffer | throw (.invalidProgram "test detached allocation lost native owner")
    modify fun state => {state with machine := {state.machine with
      user := {state.machine.user with released := state.machine.user.released.push owner.pointer}}}
  error := fun _ => .invalidProgram "deallocation failed" }

private def run (failResolve : Bool) : MachineHooks.M Unit UserState Unit :=
  AllocationMachine.deallocate (hooks failResolve)
    (Pointer.new (some (.concrete targetId tag)) Size.ZERO) none (.machine ())

def main : IO Unit := do
  let verifyDetached (result : MachineHooks.State Unit UserState) (expectedEvent : String) : IO Unit := do
    if result.machine.user.released != #[101] then
      throw (IO.userError s!"only detached owner 101 should be dropped: {reprStr result.machine.user.released}")
    if result.machine.user.events != #["resolve",expectedEvent] then
      throw (IO.userError s!"callback mutations were lost: {reprStr result.machine.user.events}")
    if result.machine.memory.live.map Prod.fst != #[survivorId] then
      throw (IO.userError "unrelated survivor memory was changed")
    if result.machine.raceAllocations.map Prod.fst != #[survivorId,resolverRemovedId,hookRemovedId] then
      throw (IO.userError s!"callback successor race entries were changed: {reprStr (result.machine.raceAllocations.map Prod.fst)}")
    if result.machine.user.registry.allocations.map Prod.fst != #[survivorId,resolverRemovedId,hookRemovedId] then
      throw (IO.userError s!"callback successor allocation extras were changed: {reprStr (result.machine.user.registry.allocations.map Prod.fst)}")
    let some resolverExtra := (result.machine.user.registry.allocations.find? (fun entry => entry.1 == resolverRemovedId)).map Prod.snd
      | throw (IO.userError "resolver callback's reinserted extras were lost")
    let some (_, resolverEntry) := resolverExtra.sync[0]? |
      throw (IO.userError "resolver callback's sync marker is missing")
    if resolverExtra.sync.size != 1 || !resolverEntry.deleteOnWrite then
      throw (IO.userError "resolver callback's marked sync entry was changed")
  let success ← machineState false
  match (run false).run success with
  | .error error _ => throw (IO.userError s!"successful deallocation failed: {reprStr error}")
  | .ok _ result => verifyDetached result "sync-success"
  let hookFailure ← machineState true
  match (run false).run hookFailure with
  | .ok _ _ => throw (IO.userError "sync failure must propagate after native drop")
  | .error error result => do
    if error != .callback "sync failure after detached removal" then
      throw (IO.userError s!"callback error ordering changed: {reprStr error}")
    verifyDetached result "sync-failure"
  let resolverFailure ← machineState false
  match (run true).run resolverFailure with
  | .ok _ _ => throw (IO.userError "resolver failure must propagate")
  | .error _ result => do
    if !result.machine.user.released.isEmpty then
      throw (IO.userError "resolver failure must not drop a non-detached owner")
    if result.machine.user.events != #["resolve"] then
      throw (IO.userError "resolver failure did not retain its mutation prefix")
    if result.machine.memory.live.map Prod.fst != #[targetId,hookRemovedId,survivorId] then
      throw (IO.userError "resolver failure lost or changed the target live allocation")
    if result.machine.raceAllocations.map Prod.fst != #[targetId,hookRemovedId,survivorId,resolverRemovedId] then
      throw (IO.userError "resolver failure lost unrelated race state")
    if result.machine.user.registry.allocations.map Prod.fst != #[targetId,hookRemovedId,survivorId,resolverRemovedId] then
      throw (IO.userError "resolver failure lost target allocation extras")
  let initialMachine ← machineState false
  let stillOwned := MemoryExtras.discardUninserted extras targetId initialMachine.machine
  if stillOwned.raceAllocations.map Prod.fst != initialMachine.machine.raceAllocations.map Prod.fst then
    throw (IO.userError "cleanup changed side tables for an allocation that is still live")
  let missingLiveOwner := {initialMachine.machine with
    memory := {initialMachine.machine.memory with
      live := initialMachine.machine.memory.live.filter (fun entry => entry.1 != targetId)}}
  match (MemoryExtras.initAllocation extras targetId false).run missingLiveOwner with
  | .ok _ _ => throw (IO.userError "duplicate extras must fail before creating another owner")
  | .error error result => do
    if error != .invalidProgram "allocation extras initialized twice" then
      throw (IO.userError s!"duplicate extras error changed: {reprStr error}")
    if result.user.registry.allocations.map Prod.fst !=
        initialMachine.machine.user.registry.allocations.map Prod.fst then
      throw (IO.userError "failed duplicate initialization deleted a preexisting registry owner")
    if result.raceAllocations.map Prod.fst != initialMachine.machine.raceAllocations.map Prod.fst then
      throw (IO.userError "failed duplicate initialization changed a preexisting race owner")
    let some (_, oldExtra) := result.user.registry.allocations.find? (fun entry => entry.1 == targetId)
      | throw (IO.userError "failed duplicate initialization lost target registry data")
    let some (_, oldEntry) := oldExtra.sync[0]? |
      throw (IO.userError "failed duplicate initialization lost target sync data")
    if oldEntry.deleteOnWrite then
      throw (IO.userError "failed duplicate initialization overwrote existing target sync data")
  let tentative := {initialMachine.machine with
    memory := {initialMachine.machine.memory with
      live := initialMachine.machine.memory.live.filter (fun entry => entry.1 != targetId)}
    allocationSpans := #[(targetId,⟨1⟩,none),(survivorId,⟨2⟩,none)]}
  let cleaned := MemoryExtras.discardUninserted extras targetId tentative
  if cleaned.raceAllocations.map Prod.fst != #[resolverRemovedId,hookRemovedId,survivorId] then
    throw (IO.userError "uninserted cleanup did not remove only its race owner")
  if cleaned.user.registry.allocations.map Prod.fst != #[resolverRemovedId,hookRemovedId,survivorId] then
    throw (IO.userError "uninserted cleanup did not remove only its allocation extras")
  if cleaned.allocationSpans.map Prod.fst != #[survivorId] then
    throw (IO.userError "uninserted cleanup did not remove only its span owner")
  IO.println "Detached native owner and callback successor: PASS"
