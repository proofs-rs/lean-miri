import Miri.Memory.MemoryState

open Miri.ABI Miri.Memory

private def check (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

private def isError : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

private def stateHook (memory : MemoryState Provenance Unit Unit) (state : α)
    (outcome : Except String β) : MemoryStateHookResult Provenance Unit Unit α β :=
  ⟨memory,state,outcome⟩

private def initFail (memory : MemoryState Provenance Unit Unit) (_state : Unit)
    (_id : AllocId) (_kind : MemoryKind Unit) (_size : Size) (_align : Align) :
    MemoryStateHookResult Provenance Unit Unit Unit Unit :=
  stateHook memory () (.error "init failure")

private def initOk (memory : MemoryState Provenance Unit Unit) (state : Unit)
    (_id : AllocId) (_kind : MemoryKind Unit) (_size : Size) (_align : Align) :
    MemoryStateHookResult Provenance Unit Unit Unit Unit := stateHook memory state (.ok ())

private def rootOk (memory : MemoryState Provenance Unit Unit) (state : Unit)
    (id : AllocId) (_kind : MemoryKind Unit) :
    MemoryStateHookResult Provenance Unit Unit Unit (Pointer Provenance) :=
  stateHook memory state (.ok (Pointer.new (.concrete id BorTag.one) Size.ZERO))

private def globalHooks : MemoryLifecycleHooks Provenance Unit Unit (Array String) Unit := {
  synchronizeMemory := fun _ state => state
  initLocalAllocation := fun memory state _ _ _ _ => stateHook memory state (.ok ())
  adjustRootPointer := fun memory state id _ =>
    stateHook memory state (.ok (Pointer.new (.concrete id BorTag.one) Size.ZERO))
  resolvePointer := fun memory state pointer _ =>
    let state := state.push "resolve"
    match pointer.provenance with
    | some (.concrete id _) => ⟨memory,state, .ok (id, pointer.offset, ())⟩
    | _ => ⟨memory,state, .error pointer.offset.bytes⟩
  beforeDeallocation := fun memory state _ _ _ _ _ _ _ => stateHook memory state (.ok ())
  copyMemory := fun state memory _ _ _ _ _ => ⟨memory, state, .ok ()⟩
}

private def storage (size : Size) (_align : Align) : Option (Array UInt8) :=
  some (Array.replicate size.bytes.toNat 0)

def main : IO Unit := do
  let empty : MemoryState Provenance Unit Unit := MemoryState.empty
  let (firstState, firstResult) := empty.reserveAllocId
  let first ← match firstResult with
    | .ok id => pure id
    | .error error => throw (IO.userError (toString error))
  let (secondState, secondResult) := firstState.reserveAllocId
  let second ← match secondResult with
    | .ok id => pure id
    | .error error => throw (IO.userError (toString error))
  check (first.value == UInt64.ofNat 1 && second.value == UInt64.ofNat 2)
    "the rustc AllocId supply must start at one and increment"
  check (secondState.issuedIds == #[first, second]) "reserved IDs must be retained"
  IO.println s!"ids first={first.value.toNat} second={second.value.toNat}"

  let maxValue := UInt64.ofNat ((2 ^ 64) - 1)
  let maxState := { empty with nextAllocId := maxValue }
  let (afterMax, maxResult) := maxState.reserveAllocId
  let maxId ← match maxResult with
    | .ok id => pure id
    | .error error => throw (IO.userError s!"u64::MAX should be a valid nonzero AllocId: {error}")
  check (maxId.value == maxValue && afterMax.nextAllocId == 0)
    "reserving u64::MAX must wrap the atomic supply to zero"
  IO.println s!"max id={maxId.value.toNat} next={afterMax.nextAllocId.toNat}"
  let (afterZero, zeroResult) := afterMax.reserveAllocId
  check (zeroResult == .error .exhausted && afterZero.idSupplyExhausted)
    "the source's NonZero unwrap at zero must be explicit and terminal"
  IO.println s!"zero panic={isError zeroResult} next={afterZero.nextAllocId.toNat}"

  let collisionState := { firstState with nextAllocId := first.value }
  let (afterCollision, collisionResult) := collisionState.reserveAllocId
  check (collisionResult == .error (.alreadyIssued first))
    "a wrapped/corrupt ID supply must not issue a colliding runtime ID"
  check (afterCollision.nextAllocId == first.value + 1)
    "failed collision detection must retain fetch_add's state advance"

  let importResult := MemoryLifecycle.registerImportedGlobal empty () 73
      .memory (Size.ofBytes 12) Align.ONE
  let importedId ← match importResult.outcome with
    | .ok id => pure id
    | .error error => throw (IO.userError (toString error))
  let importedMemory := importResult.memory
  check (importedMemory.runtimeIdForExport? 73 == some importedId)
    "export graph IDs must map explicitly to runtime AllocIds"
  check (importedId.value == UInt64.ofNat 1 && importedMemory.issuedIds == #[importedId])
    "imported globals must consume the same runtime ID supply"
  let globalPointer := Pointer.new (.concrete importedId BorTag.one) Size.ZERO
  let globalFree := MemoryLifecycle.deallocatePtr importedMemory #[]
      globalPointer.withOptionalProvenance none .stack globalHooks
  check (globalFree.outcome == .error (.globalAllocationDeallocation importedId .memory) &&
      globalFree.memory.globals.size == 1)
    "global deallocation must consult owned global metadata and leave it installed"
  IO.println s!"global-deallocation live={globalFree.memory.live.size} dead={globalFree.memory.dead.size} issued={globalFree.memory.issuedIds.size} error={isError globalFree.outcome} events={String.intercalate "," globalFree.hooks.toList}"
  let localResult := MemoryLifecycle.allocatePtr importedMemory () (fun _ state => state) (Size.ofBytes 4) Align.ONE
      (.machine ()) .Zero (Size.ofBytes 32) none storage initOk rootOk
  let localPointer ← match localResult.outcome with
    | .ok pointer => pure pointer
    | .error error => throw (IO.userError (toString error))
  let localId ← match localPointer.provenance with
    | .concrete id _ => pure id
    | .wildcard => throw (IO.userError "local allocation unexpectedly returned wildcard provenance")
  check (localId.value == UInt64.ofNat 2 &&
      (localResult.memory.findGlobal? importedId).isSome)
    "a local allocation must not collide with an imported global"
  check (localResult.memory.runtimeIdForExport? 73 == some importedId)
    "local allocation must preserve the exporter-ID mapping"

  let duplicate := MemoryLifecycle.registerImportedGlobal importedMemory () 73
      .static Size.ZERO Align.ONE
  check (duplicate.outcome == .error (.metadataError (.duplicateExportId 73)))
    "duplicate exporter IDs must be rejected"
  check (duplicate.memory.issuedIds == importedMemory.issuedIds)
    "duplicate exporter IDs must fail before reserving another runtime ID"

  let initFailure := MemoryLifecycle.allocatePtr empty () (fun _ state => state) (Size.ofBytes 4) Align.ONE
      (.machine ()) .Zero (Size.ofBytes 32) none storage initFail rootOk
  check (isError initFailure.outcome && initFailure.memory.issuedIds.size == 1 &&
      initFailure.memory.live.size == 0)
    "init-hook failure must consume the reserved ID without inserting a live allocation"

  let tooLarge := MemoryLifecycle.allocatePtr empty () (fun _ state => state) (Size.ofBytes 4) Align.ONE
      (.machine ()) .Zero (Size.ofBytes 2) none storage initOk rootOk
  check (isError tooLarge.outcome && tooLarge.memory.issuedIds.size == 0)
    "the object-size assertion must run before ID reservation"

  let dynamicGlobal := MemoryLifecycle.allocatePtr empty () (fun _ state => state) (Size.ofBytes 4) Align.ONE
      (.machine ()) .Zero (Size.ofBytes 32) (some (.machine ())) storage initOk rootOk
  check (isError dynamicGlobal.outcome && dynamicGlobal.memory.issuedIds.size == 1)
    "the dynamically-global debug assertion occurs after ID reservation"

  let hostFailure := MemoryLifecycle.allocatePtr empty () (fun _ state => state) (Size.ofBytes 4) Align.ONE
      (.machine ()) .Zero (Size.ofBytes 32) none (fun _ _ => none) initOk rootOk
  check (isError hostFailure.outcome && hostFailure.memory.issuedIds.size == 0)
    "fallible host allocation failure must occur before ID reservation"

  IO.println "AllocId supply, exhaustion, global mapping, and reservation ordering passed"
