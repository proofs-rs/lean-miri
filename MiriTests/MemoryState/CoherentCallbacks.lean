import Miri.Memory.MemoryState

open Miri.ABI Miri.Memory

private abbrev Mem := MemoryState Provenance Unit Unit

private structure Nested where
  memory : Mem
  events : Array String := #[]
  failAt : String := ""


private def mark (state : Nested) (event : String) : Nested :=
  { state with events := state.events.push event }

private def coherent (state : Nested) (memory : Mem) : Bool :=
  state.memory.nextAllocId == memory.nextAllocId &&
    state.memory.issuedIds == memory.issuedIds &&
    state.memory.live.size == memory.live.size

private def sync (memory : Mem) (state : Nested) : Nested := {state with memory}

private def mutate (memory : Mem) : Mem := go memory 4
where
  go (memory : Mem) : Nat → Mem
    | 0 => (memory.reserveAllocId).1
    | fuel + 1 =>
        let (next, result) := memory.reserveAllocId
        match result with
        | .ok _ => next
        | .error _ => go next fuel

private def copyHooks : MemoryCopyHooks Provenance Unit Unit Nested Unit := {
  synchronizeMemory := sync
  pointerAccess := fun memory state pointer size =>
    let event := if state.events.isEmpty then "pointer-source" else "pointer-destination"
    let state := mark state (if coherent state memory then event else "stale:" ++ event)
    let changed := mutate memory
    let fails := state.failAt == event
    match pointer.provenance with
    | some (.concrete id _) =>
        if fails then ⟨changed,state,.error (event ++ " failure")⟩
        else if size.bytes == 0 then ⟨changed,state,.ok none⟩
        else ⟨changed,state,.ok (some (id,pointer.offset,()))⟩
    | _ => ⟨changed,state,.error "unresolved pointer"⟩
  tryGetAllocId := fun memory state pointer _ =>
    if coherent state memory then pointer.provenance.bind fun
      | .concrete id _ => some id
      | .wildcard => none
    else none
  beforeAllocationAccess := fun memory state _ =>
    let state := mark state (if coherent state memory then "alloc" else "stale:alloc")
    let changed := mutate memory
    if state.failAt == "alloc" then ⟨changed,state,.error "allocation failure"⟩
    else ⟨changed,state,.ok ()⟩
  beforeMemoryRead := fun state memory _ _ _ _ _ =>
    let state := mark state (if coherent state memory then "read" else "stale:read")
    let changed := mutate memory
    if state.failAt == "read" then ⟨changed,state,.error "read failure"⟩
    else ⟨changed,state,.ok ()⟩
  beforeMemoryWrite := fun state memory _ _ _ _ _ =>
    let state := mark state (if coherent state memory then "write" else "stale:write")
    let changed := mutate memory
    if state.failAt == "write" then ⟨changed,state,.error "write failure"⟩
    else ⟨changed,state,.ok ()⟩
}

private def storage (size : Size) (_align : Align) : Option (Array UInt8) :=
  some (Array.replicate size.bytes.toNat 0)

private def memoryWithTwo : IO (Mem × AllocId × AllocId) := do
  let sourceId ← match AllocId.ofUInt64 1 with
    | some id => pure id
    | none => throw (IO.userError "source ID")
  let destId ← match AllocId.ofUInt64 2 with
    | some id => pure id
    | none => throw (IO.userError "destination ID")
  let source ← match Allocation.fromBytes (Prov := Provenance) #[7] Align.ONE .Not with
    | .ok allocation => pure allocation
    | .error error => throw (IO.userError (toString error))
  let dest ← match Allocation.fromBytes (Prov := Provenance) #[0] Align.ONE .Mut with
    | .ok allocation => pure allocation
    | .error error => throw (IO.userError (toString error))
  let state : Mem := { (MemoryState.empty : Mem) with
    live := #[(sourceId,⟨.machine (),source⟩),(destId,⟨.machine (),dest⟩)] }
  pure (state,sourceId,destId)

private def ptr (id : AllocId) (offset : Nat) : Pointer (Option Provenance) :=
  Pointer.new (some (.concrete id BorTag.one)) (Size.ofBytes (UInt64.ofNat offset))

private def ensure (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def allocationCallbacks (failAt : String) :=
  let init := fun (memory : Mem) (state : Nested) (id : AllocId) (_kind : MemoryKind Unit)
      (_size : Size) (_align : Align) =>
    let state := mark state (if coherent state memory then "init" else "stale:init")
    let changed := mutate memory
    if failAt == "init" then
      ({memory := changed,state,outcome := .error "init failure"} :
        MemoryStateHookResult Provenance Unit Unit Nested Unit)
    else ({memory := changed,state,outcome := .ok ()} :
      MemoryStateHookResult Provenance Unit Unit Nested Unit)
  let root := fun (memory : Mem) (state : Nested) (id : AllocId) (_kind : MemoryKind Unit) =>
    let visible := coherent state memory && memory.live.any (fun entry => entry.1 == id)
    let state := mark state (if visible then "root" else "stale:root")
    let changed := mutate memory
    if failAt == "root" then
      ({memory := changed,state,outcome := .error "root failure"} :
        MemoryStateHookResult Provenance Unit Unit Nested (Pointer Provenance))
    else ({memory := changed,state,outcome := .ok (Pointer.new (.concrete id BorTag.one) Size.ZERO)} :
      MemoryStateHookResult Provenance Unit Unit Nested (Pointer Provenance))
  (init,root)

def main : IO Unit := do
  let (initial,sourceId,destId) ← memoryWithTwo
  let start : Nested := ⟨initial, #[], ""⟩
  let copied := MemoryLifecycle.memCopyRepeatedly initial start (ptr sourceId 0)
    (ptr destId 0) (Size.ofBytes 1) 1 true (Size.ofBytes 8) copyHooks
  ensure ((match copied.outcome with | .ok () => true | .error _ => false)) "nested-state copy should succeed"
  ensure (copied.hooks.events == #["pointer-source","pointer-destination","alloc","read","alloc","write"])
    s!"callbacks observed stale or reordered machine memory: {copied.hooks.events}"
  ensure (coherent copied.hooks copied.memory) "success result must synchronize embedded machine memory"
  ensure (copied.memory.issuedIds.size == 6) "all six nested memory mutations must survive copy"
  let bytes := (copied.memory.live.find? (fun entry => entry.1 == destId)).map fun entry =>
    entry.2.allocation.getBytesUnchecked (allocRange Size.ZERO (Size.ofBytes 1))
  ensure (bytes == some (.ok #[7])) "copy storage update must follow callback memory mutations"

  let failStart : Nested := {start with failAt := "pointer-source"}
  let failed := MemoryLifecycle.memCopyRepeatedly initial failStart (ptr sourceId 0)
    (ptr destId 0) (Size.ofBytes 1) 1 true (Size.ofBytes 8) copyHooks
  ensure (failed.outcome == .error (.hookFailure "getPtrAccess(source)" "pointer-source failure"))
    "source pointer failure kind/prefix changed"
  ensure (failed.memory.issuedIds.size == 1 && failed.hooks.events == #["pointer-source"])
    "source pointer failure must retain its mutation and stop later callbacks"
  ensure (coherent failed.hooks failed.memory) "failed result must synchronize embedded machine memory"

  let (initCallback,rootCallback) := allocationCallbacks ""
  let allocated := MemoryLifecycle.allocatePtr (MemoryState.empty : Mem) ⟨MemoryState.empty, #[], ""⟩
    sync (Size.ofBytes 1) Align.ONE (.machine ()) .Zero (Size.ofBytes 8) none storage
    initCallback rootCallback
  ensure (match allocated.outcome with | .ok _ => true | .error _ => false)
    "nested-state allocation should succeed"
  ensure (allocated.hooks.events == #["init","root"] && coherent allocated.hooks allocated.memory)
    "init/root callbacks must see inserted memory and return the final embedded view"
  ensure (allocated.memory.issuedIds.size == 3 && allocated.memory.live.size == 1)
    "reservation, init mutation, and root mutation must all survive allocation"

  let (failingInit,unusedRoot) := allocationCallbacks "init"
  let initFailed := MemoryLifecycle.allocatePtr (MemoryState.empty : Mem)
    ⟨MemoryState.empty, #[], ""⟩ sync (Size.ofBytes 1) Align.ONE (.machine ()) .Zero
    (Size.ofBytes 8) none storage failingInit unusedRoot
  ensure (initFailed.outcome == .error (.hookFailure "initLocalAllocation" "init failure"))
    "init failure kind or stage changed"
  ensure (initFailed.memory.issuedIds.size == 2 && initFailed.memory.live.isEmpty &&
      initFailed.hooks.events == #["init"] && coherent initFailed.hooks initFailed.memory)
    "init failure must retain reservation and initializer mutation only"

  let (goodInit,failingRoot) := allocationCallbacks "root"
  let rootFailed := MemoryLifecycle.allocatePtr (MemoryState.empty : Mem)
    ⟨MemoryState.empty, #[], ""⟩ sync (Size.ofBytes 1) Align.ONE (.machine ()) .Zero
    (Size.ofBytes 8) none storage goodInit failingRoot
  ensure (rootFailed.outcome == .error (.hookFailure "adjustAllocRootPointer" "root failure"))
    "root failure kind or stage changed"
  ensure (rootFailed.memory.issuedIds.size == 3 && rootFailed.memory.live.size == 1 &&
      rootFailed.hooks.events == #["init","root"] && coherent rootFailed.hooks rootFailed.memory)
    "root failure must retain insertion and its callback mutation"
  IO.println "coherent-copy success and source-failure prefixes passed"
