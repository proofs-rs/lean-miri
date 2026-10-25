import Miri.Memory.MemoryState

open Miri.ABI Miri.Memory

private structure NestedRecord where
  events : Array Nat := #[0]
  deriving DecidableEq, Repr

private structure AuditExtra where
  child : NestedRecord := {}
  deriving DecidableEq, Repr

private def check (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

private def hasError : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

private def targetId : AllocId := ⟨1, by decide⟩
private def sentinelId : AllocId := ⟨2, by decide⟩

private def makeAllocation (extra : AuditExtra) : Except AllocError (Allocation Provenance AuditExtra) := do
  let bytes := Array.replicate 4 (0 : UInt8)
  let allocation ← Allocation.fromBytes (Prov := Provenance) bytes Align.ONE .Mut
  pure (allocation.withExtra extra)

private def initialMemory : IO (MemoryState Provenance AuditExtra Unit) := do
  let first := targetId
  let second := sentinelId
  let firstAllocation ← match makeAllocation {} with
    | .ok allocation => pure allocation
    | .error error => throw (IO.userError (toString error))
  let secondAllocation ← match makeAllocation {} with
    | .ok allocation => pure allocation
    | .error error => throw (IO.userError (toString error))
  let issued := MemoryState.setIssuedIds
    (MemoryState.empty : MemoryState Provenance AuditExtra Unit) #[first, second]
  pure {issued with
    nextAllocId := 3
    live := #[(first, ⟨.machine (), firstAllocation⟩),
      (second, ⟨.machine (), secondAllocation⟩)] }

private def appendNested (memory : MemoryState Provenance AuditExtra Unit)
    (id : AllocId) (value : Nat) : MemoryState Provenance AuditExtra Unit :=
  match memory.live.find? (fun entry => entry.1 == id) with
  | none => memory
  | some (_, entry) =>
      let old := entry.allocation.extra
      let nested := {old.child with events := old.child.events.push value}
      match memory.setLiveAllocation id (entry.allocation.setExtra {old with child := nested}) with
      | .ok memory => memory
      | .error _ => memory

private def nestedEvents (memory : MemoryState Provenance AuditExtra Unit)
    (id : AllocId) : Array Nat :=
  ((memory.live.find? (fun entry => entry.1 == id)).map
      (fun entry => entry.2.allocation.extra.child.events)).getD #[]

private def deallocationHooks (failResolve failBefore : Bool) :
    MemoryDeallocationHooks Provenance AuditExtra Unit (Array String) Unit := {
  synchronizeMemory := fun _ state => state
  resolvePointer := fun memory state pointer _ =>
    let memory := appendNested memory sentinelId 1
    let state := state.push "resolve"
    if failResolve then ⟨memory, state, .error pointer.offset.bytes⟩
    else ⟨memory, state, .ok (targetId, pointer.offset, ())⟩
  beforeDeallocation := fun memory state _ _ _ _ _ _ _ =>
    let memory := appendNested memory sentinelId 2
    let state := state.push "before"
    if failBefore then ⟨memory, state, .error "deallocation callback failure"⟩
    else ⟨memory, state, .ok ()⟩ }

private def run (failResolve failBefore : Bool)
    (oldLayout : Option (Size × Align) := none) := do
  let memory ← initialMemory
  pure (MemoryLifecycle.deallocatePtrWith memory #[]
    (Pointer.new (some (.concrete targetId BorTag.one)) Size.ZERO) oldLayout (.machine ())
    (deallocationHooks failResolve failBefore))

def main : IO Unit := do
  let success ← run false false
  check (success.outcome.isOk) "successful deallocation must complete"
  check (success.memory.live.all (fun entry => entry.1 != targetId))
    "successful deallocation must remove the target allocation"
  check (success.memory.dead.any (fun entry => entry.allocId == targetId))
    "successful deallocation must cache the dead allocation after callbacks"
  check (success.detached.map Prod.fst == some targetId)
    "success must return the exact local owner removed by the lifecycle"
  check (success.detached.map (fun entry =>
      entry.2.allocation.byteSize == Size.ofBytes 4 &&
        entry.2.allocation.extra.child.events == #[0]) == some true)
    "success must preserve the removed allocation value, not a later map projection"
  check (nestedEvents success.memory sentinelId == #[0, 1, 2])
    "resolver and before-hook nested mutations must survive a successful deallocation"
  check (success.hooks == #["resolve", "before"])
    "success must retain source-ordered resolver and before-hook events"

  let layoutFailure ← run false false (some (Size.ofBytes 7, Align.ONE))
  check (hasError layoutFailure.outcome) "layout failure must propagate"
  check (layoutFailure.detached.map Prod.fst == some targetId)
    "layout failure must return the owner removed before validation"
  check (layoutFailure.detached.map (fun entry =>
      entry.2.allocation.byteSize == Size.ofBytes 4 &&
        entry.2.allocation.extra.child.events == #[0]) == some true)
    "layout failure must retain the original removed allocation owner"
  check (layoutFailure.memory.live.all (fun entry => entry.1 != targetId))
    "layout failure must retain the already-removed live-map prefix"
  check (layoutFailure.memory.dead.isEmpty)
    "layout failure must skip dead-allocation insertion"
  check (layoutFailure.hooks == #["resolve"])
    "layout failure must skip the before-deallocation callback"

  let beforeFailure ← run false true
  check (hasError beforeFailure.outcome) "before-hook failure must propagate"
  check (beforeFailure.memory.live.all (fun entry => entry.1 != targetId))
    "before-hook failure must retain the earlier live-map removal"
  check (beforeFailure.memory.dead.isEmpty)
    "before-hook failure must skip dead-allocation insertion"
  check (beforeFailure.detached.map Prod.fst == some targetId)
    "before-hook failure must retain ownership of the exact removed allocation"
  check (nestedEvents beforeFailure.memory sentinelId == #[0, 1, 2])
    "before-hook failure must retain all nested callback mutations"
  check (beforeFailure.hooks == #["resolve", "before"])
    "before-hook failure must retain both callback event prefixes"

  let resolveFailure ← run true false
  check (hasError resolveFailure.outcome) "resolver failure must propagate"
  check (resolveFailure.memory.live.any (fun entry => entry.1 == targetId))
    "resolver failure must occur before live-map removal"
  check (resolveFailure.memory.dead.isEmpty)
    "resolver failure must not insert dead-allocation metadata"
  check (resolveFailure.detached.isNone)
    "resolver failure must not fabricate a detached allocation owner"
  check (nestedEvents resolveFailure.memory sentinelId == #[0, 1])
    "resolver failure must retain its nested mutation prefix only"
  check (resolveFailure.hooks == #["resolve"])
    "resolver failure must skip the before-deallocation callback"

  IO.println "Coherent deallocation callback successors: PASS"
