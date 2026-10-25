import Miri.TreeBorrows.MachineMemoryHooks

open Miri.ABI
open Miri.Memory
open Miri.TreeBorrows
open Miri.TreeBorrows.MachineMemoryHooks

structure TestState where
  events : Array String := #[]
  deriving Repr

private def emit (state : TestState) (event : String) : TestState :=
  { state with events := state.events.push event }

private def eventText (events : Array String) : String :=
  String.intercalate "," events.toList

private def syncKindText : SyncAccessKind → String
  | .Read => "read"
  | .Write => "write"
  | .Dealloc => "dealloc"

private def hooks (failSyncObject : Option Nat := none) (failWriteRace : Bool := false) :
    Hooks TestState Nat Unit := {
  protectedTags := {}
  emitDiagnostic := fun state _ diagnostic =>
    emit state (match diagnostic with
      | .Read _ => "diagnostic:read"
      | .Write _ => "diagnostic:write"
      | .Freed => "diagnostic:freed")
  dataRaceRead := fun state _ _ _ => ⟨emit state "race:read", .ok ()⟩
  dataRaceWrite := fun state _ _ _ =>
    let state := emit state "race:write"
    if failWriteRace then ⟨state, .error "race"⟩ else ⟨state, .ok ()⟩
  dataRaceDeallocate := fun state _ _ _ _ => ⟨emit state "race:dealloc", .ok ()⟩
  syncOnAccess := fun state object kind =>
    let state := emit state s!"sync:{syncKindText kind}:{object}"
    if failSyncObject == some object then ⟨state, .error "blocked"⟩
    else ⟨state, .ok ()⟩
  deleteOnWrite := fun object => object == 10
  recordDeallocatedSpan := fun state _ => emit state "span:deallocated"
  freeAllocId := fun state _ _ _ _ => emit state "free:alloc-id"
}

private def allocId1 : AllocId := ⟨1, by decide⟩
private def allocId2 : AllocId := ⟨2, by decide⟩
private def tag2 : BorTag := ⟨2, by decide⟩

private def treeMemory : Except AllocError (MemoryState Provenance BorrowTree Unit) := do
  let firstBytes ← Allocation.fromBytes #[7, 8, 9] Align.ONE .Mut
  let secondBytes ← Allocation.fromBytes #[0, 0, 0] Align.ONE .Mut
  let first := firstBytes.withExtra (BorrowTree.new BorTag.one (Size.ofBytes 3))
  let second := secondBytes.withExtra (BorrowTree.new tag2 (Size.ofBytes 3))
  let firstEntry : LocalAllocation Provenance BorrowTree Unit := ⟨.stack, first⟩
  let secondEntry : LocalAllocation Provenance BorrowTree Unit := ⟨.stack, second⟩
  let initial : MemoryState Provenance BorrowTree Unit := MemoryState.empty
  let issued := MemoryState.setIssuedIds initial #[allocId1, allocId2]
  return {issued with live := #[(allocId1, firstEntry), (allocId2, secondEntry)]}

private def syncStore : SyncObjectStore Nat := Id.run do
  let first : SyncObjectMap Nat :=
    (SyncObjectMap.empty.insert (Size.ofBytes 2) 20).insert (Size.ofBytes 0) 10
  let second : SyncObjectMap Nat := SyncObjectMap.empty.insert (Size.ofBytes 0) 20
  return (SyncObjectStore.empty.set allocId1 first).set allocId2 second

private def context (state : TestState := ({} : TestState)) : Context TestState Nat := {
  state
  syncObjects := syncStore
  trackAllocAccesses := true
  trackedAllocIds := #[allocId1, allocId2]
}

private def pointer (allocId : AllocId) (tag : BorTag) : Pointer (Option Provenance) :=
  Pointer.withOptionalProvenance (Pointer.new (.concrete allocId tag) Size.ZERO)

private def requireCheck (condition : Bool) (message : String) : IO Unit := do
  if !condition then throw (IO.userError message)

def main : IO Unit := do
  let memory ← match treeMemory with
    | .ok memory => pure memory
    | .error error => throw (IO.userError s!"allocation setup failed: {error}")

  let pointerAccess := fun mem state (ptr : Pointer (Option Provenance)) (_size : Size) =>
    match ptr.provenance with
    | some (.concrete id tag) =>
        ⟨mem,state,.ok (some (id, ptr.offset, .concrete tag))⟩
    | some .wildcard | none => ⟨mem,state,.ok none⟩
  let tryGetAllocId := fun (_mem : MemoryState Provenance BorrowTree Unit)
      (_state : Context TestState Nat)
      (ptr : Pointer (Option Provenance)) (_size : UInt64) =>
    match ptr.provenance with
    | some (.concrete id _) => some id
    | some .wildcard | none => none
  let beforeAllocationAccess := fun mem state (_id : AllocId) =>
    ⟨mem,{ state with state := emit state.state "alloc-access" },.ok ()⟩
  let copyHooks := asMemoryCopyHooks (hooks none) pointerAccess tryGetAllocId
      beforeAllocationAccess
  let copied := MemoryLifecycle.memCopyRepeatedly memory (context ({} : TestState))
      (pointer allocId1 BorTag.one) (pointer allocId2 tag2) (Size.ofBytes 1) 1
      true (Size.ofBytes 8) copyHooks
  requireCheck (copied.outcome == .ok ()) "mem-copy machine hook adapter should succeed"
  requireCheck (copied.hooks.state.events == #[
      "alloc-access", "diagnostic:read", "race:read", "sync:read:10",
      "alloc-access", "diagnostic:write", "race:write", "sync:write:20"])
    "mem-copy should invoke allocation, race, Tree Borrows, and sync hooks in source order"
  let destSync := copied.hooks.syncObjects.get allocId2
  requireCheck (destSync.entries.size == 1 && destSync.entries[0]?.map Prod.snd == some 20)
    "successful write should delete only sync objects whose delete_on_write is true"
  requireCheck (eventText copied.hooks.state.events |>.contains "sync:write:20")
    "mem-copy write should invoke the destination sync object"

  let some firstEntry := memory.live[0]?
    | throw (IO.userError "test source allocation is missing")
  let firstAllocation := firstEntry.2.allocation
  let successfulWrite := beforeMemoryWrite memory (context ({} : TestState)) (hooks none)
      firstAllocation (pointer allocId1 BorTag.one) allocId1 (.concrete BorTag.one)
      (allocRange Size.ZERO (Size.ofBytes 3))
  let writeSync := successfulWrite.context.syncObjects.get allocId1
  requireCheck (successfulWrite.outcome == .ok () && writeSync.entries.size == 1 &&
      writeSync.entries[0]?.map Prod.snd == some 20)
    "successful write should remove the checked delete_on_write object"
  requireCheck (successfulWrite.context.state.events == #[
      "diagnostic:write", "race:write", "sync:write:10", "sync:write:20"])
    "successful write should finish all sync checks before deleting sync metadata"

  let writeFailure := beforeMemoryWrite memory (context ({} : TestState)) (hooks (some 20))
      firstAllocation (pointer allocId1 BorTag.one) allocId1 (.concrete BorTag.one)
      (allocRange Size.ZERO (Size.ofBytes 3))
  requireCheck (match writeFailure.outcome with | .error _ => true | .ok _ => false)
    "the second sync write check should fail"
  requireCheck ((writeFailure.context.syncObjects.get allocId1).entries.size == 2)
    "a failed sync check must prevent all collected delete_on_write removals"
  requireCheck (writeFailure.context.state.events == #[
      "diagnostic:write", "race:write", "sync:write:10", "sync:write:20"])
    "a failed sync check must stop the ordered sync walk"

  let raceFailure := beforeMemoryWrite memory (context ({} : TestState)) (hooks none true)
      firstAllocation (pointer allocId1 BorTag.one) allocId1 (.concrete BorTag.one)
      (allocRange Size.ZERO (Size.ofBytes 1))
  requireCheck (match raceFailure.outcome with | .error _ => true | .ok _ => false)
    "data-race failure should stop the write before Tree Borrows"
  requireCheck (raceFailure.context.state.events == #["diagnostic:write", "race:write"] &&
      (raceFailure.memory.live[0]?).map (fun entry =>
        entry.2.allocation.extra == firstAllocation.extra) == some true)
    "data-race failure must precede Tree Borrows and sync-object updates"

  let deallocation := beforeMemoryDeallocation (context ({} : TestState)) (hooks none) firstAllocation
      (pointer allocId1 BorTag.one) allocId1 (.concrete BorTag.one) (Size.ofBytes 3)
      Align.ONE .stack
  requireCheck (deallocation.outcome == .ok ()) "unprotected root deallocation should succeed"
  requireCheck (deallocation.context.state.events == #[
      "diagnostic:freed", "race:dealloc", "sync:dealloc:10", "sync:dealloc:20",
      "span:deallocated", "free:alloc-id"])
    "deallocation hooks should preserve race/tree/sync/span/free source order"
  requireCheck ((deallocation.context.syncObjects.get allocId1).entries.isEmpty)
    "successful deallocation should discard this allocation's sync-object map"

  let missingTag := (⟨99, by decide⟩ : BorTag)
  let missing := beforeMemoryRead memory (context ({} : TestState)) (hooks none) firstAllocation
      (pointer allocId1 missingTag) allocId1 (.concrete missingTag)
      (allocRange Size.ZERO (Size.ofBytes 1))
  requireCheck (match missing.outcome with | .error _ => true | .ok _ => false)
    "a missing provenance tag must be rejected by Tree Borrows"
  requireCheck (missing.context.state.events == #["diagnostic:read", "race:read"])
    "Tree Borrows failure must occur after race handling and before sync-object checks"

  let rootIndex : UniIndex := ⟨0⟩
  let firstLocation : LocationTree := {
    perms := ({} : UniValMap Tree.LocationState).insert rootIndex
      ⟨.ReservedFrz false, false, .None⟩ }
  let secondLocation : LocationTree := {
    perms := ({} : UniValMap Tree.LocationState).insert rootIndex
      ⟨.Frozen, false, .None⟩ }
  let initialTree := BorrowTree.new BorTag.one (Size.ofBytes 3)
  let firstRange := initialTree.locations.modifyRange Size.ZERO (Size.ofBytes 1)
      (fun _ _ => firstLocation)
  let secondRange := firstRange.state.modifyRange (Size.ofBytes 1) (Size.ofBytes 2)
      (fun _ _ => secondLocation)
  let failingTree := { initialTree with locations := secondRange.state }
  let failingAllocation := firstAllocation.setExtra failingTree
  let failingMemory ← match memory.setLiveAllocation allocId1 failingAllocation with
    | .ok memory => pure memory
    | .error error => throw (IO.userError s!"test tree update failed: {reprStr error}")
  let partialTreeFailure := beforeMemoryWrite failingMemory (context ({} : TestState))
      (hooks none) failingAllocation (pointer allocId1 BorTag.one) allocId1
      (.concrete BorTag.one) (allocRange Size.ZERO (Size.ofBytes 3))
  requireCheck (match partialTreeFailure.outcome with
      | .error message => message.contains "Tree Borrows write failed"
      | .ok _ => false)
    "the second range should trigger a Tree Borrows write error"
  let some updatedEntry := partialTreeFailure.memory.live.find? fun entry => entry.1 == allocId1
    | throw (IO.userError "Tree Borrows failure dropped the live allocation")
  let firstSavedLocation := updatedEntry.2.allocation.extra.locations.iterAll[0]?.map (·.data)
    |>.getD (default : LocationTree)
  let firstSavedState := firstSavedLocation.perms.get rootIndex
  requireCheck (firstSavedState.map (·.permission) == some .Unique &&
      partialTreeFailure.context.state.events == #["diagnostic:write", "race:write"])
    "a failed later range must retain the earlier tree transition and skip sync checks"
  IO.println "machine-memory-hooks diagnostic>data-race>tree-borrows>sync>delete-or-free"
