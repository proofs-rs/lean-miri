import Miri.Memory.MemoryState

open Miri.ABI Miri.Memory

private structure CopyTrace where
  events : Array String := #[]
  fail : String := ""

private def emit (state : CopyTrace) (name : String) : CopyTrace :=
  { state with events := state.events.push name }

private def copyHooks : MemoryCopyHooks Provenance Unit Unit CopyTrace Unit := {
  synchronizeMemory := fun _ state => state
  pointerAccess := fun memory state pointer size =>
    let state := emit state "access"
    match pointer.provenance with
    | some (.concrete id _) =>
        if size.bytes == 0 then ⟨memory,state,.ok none⟩
        else ⟨memory,state,.ok (some (id, pointer.offset, ()))⟩
    | _ => ⟨memory,state,.error "unresolved pointer"⟩
  tryGetAllocId := fun _ _ pointer _ =>
    match pointer.provenance with
    | some (.concrete id _) => some id
    | _ => none
  beforeAllocationAccess := fun memory state id =>
    ⟨memory,emit state s!"alloc-{id.value}",.ok ()⟩
  beforeMemoryRead := fun state memory _allocation _pointer _id _extra _range =>
    let state := emit state "read"
    if state.fail == "read" then ⟨memory, state, .error "read hook"⟩
    else ⟨memory, state, .ok ()⟩
  beforeMemoryWrite := fun state memory _allocation _pointer _id _extra _range =>
    let state := emit state "write"
    if state.fail == "write" then ⟨memory, state, .error "write hook"⟩
    else ⟨memory, state, .ok ()⟩
}

private def twoBlocks : IO (MemoryState Provenance Unit Unit) := do
  let some sourceId := AllocId.ofUInt64 1
    | throw (IO.userError "invalid source ID")
  let some destId := AllocId.ofUInt64 2
    | throw (IO.userError "invalid destination ID")
  let source ← match Allocation.fromBytes (Prov := Provenance) #[10, 20] Align.ONE .Not with
    | .ok allocation => pure allocation
    | .error error => throw (IO.userError (toString error))
  let dest ← match Allocation.fromBytes (Prov := Provenance) (Array.replicate 4 0)
      Align.ONE .Mut with
    | .ok allocation => pure allocation
    | .error error => throw (IO.userError (toString error))
  let sourceEntry : LocalAllocation Provenance Unit Unit := ⟨.machine (), source⟩
  let destEntry : LocalAllocation Provenance Unit Unit := ⟨.machine (), dest⟩
  return { (MemoryState.empty : MemoryState Provenance Unit Unit) with
    live := #[(sourceId, sourceEntry), (destId, destEntry)] }

private def ptr (id : AllocId) (offset : UInt64 := 0) : Pointer (Option Provenance) :=
  Pointer.new (some (.concrete id BorTag.one)) (Size.ofBytes offset)

private def requireBytes (memory : MemoryState Provenance Unit Unit) (id : AllocId)
    (range : AllocRange) : IO (Array UInt8) := do
  let some entry := memory.live.find? fun item => item.1 == id
    | throw (IO.userError "expected local allocation is absent")
  match entry.2.allocation.getBytesUnchecked range with
  | .ok bytes => pure bytes
  | .error error => throw (IO.userError (toString error))

private def traceText (trace : CopyTrace) : String := String.intercalate "," trace.events.toList

private def succeeded : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

def main : IO Unit := do
  let memory ← twoBlocks
  let some sourceId := AllocId.ofUInt64 1
    | throw (IO.userError "invalid source ID")
  let some destId := AllocId.ofUInt64 2
    | throw (IO.userError "invalid destination ID")

  let copied := MemoryLifecycle.memCopyRepeatedly memory {} (ptr sourceId) (ptr destId)
      (Size.ofBytes 2) 2 true (Size.ofBytes 8) copyHooks
  match copied.outcome with
  | .error error => throw (IO.userError s!"copy bridge failed: {error}")
  | .ok () => pure ()
  let bytes ← requireBytes copied.memory destId (allocRange Size.ZERO (Size.ofBytes 4))
  if bytes != #[10, 20, 10, 20] then
    throw (IO.userError s!"copy bridge byte result was {bytes}")
  if copied.hooks.events != #["access", "access", "alloc-1", "read", "alloc-2", "write"] then
    throw (IO.userError s!"copy bridge hook order changed: {copied.hooks.events}")
  IO.println s!"copy {traceText copied.hooks} bytes={bytes.size}"

  let zeroSource := MemoryLifecycle.memCopyRepeatedly memory {} (ptr sourceId) (ptr destId)
      Size.ZERO 1 true (Size.ofBytes 8) copyHooks
  if !succeeded zeroSource.outcome then
    throw (IO.userError "zero-sized source copy failed")
  if zeroSource.hooks.events != #["access", "access", "alloc-1"] then
    throw (IO.userError s!"zero-source hook order changed: {zeroSource.hooks.events}")
  IO.println s!"zero-source {traceText zeroSource.hooks}"

  let zeroDestination := MemoryLifecycle.memCopyRepeatedly memory {} (ptr sourceId) (ptr destId)
      (Size.ofBytes 2) 0 true (Size.ofBytes 8) copyHooks
  if !succeeded zeroDestination.outcome then
    throw (IO.userError "zero-copy-count operation failed")
  if zeroDestination.hooks.events != #["access", "access", "alloc-1", "read"] then
    throw (IO.userError s!"zero-destination hook order changed: {zeroDestination.hooks.events}")
  IO.println s!"zero-destination {traceText zeroDestination.hooks}"

  let readFailure := MemoryLifecycle.memCopyRepeatedly memory { fail := "read" }
      (ptr sourceId) (ptr destId) (Size.ofBytes 2) 1 true (Size.ofBytes 8) copyHooks
  if !match readFailure.outcome with | .error _ => true | .ok _ => false then
    throw (IO.userError "read-hook failure was ignored")
  if readFailure.hooks.events != #["access", "access", "alloc-1", "read"] then
    throw (IO.userError "read-hook failure ran a later copy stage")
  IO.println s!"read-failure {traceText readFailure.hooks}"

  let writeFailure := MemoryLifecycle.memCopyRepeatedly memory { fail := "write" }
      (ptr sourceId) (ptr destId) (Size.ofBytes 2) 1 true (Size.ofBytes 8) copyHooks
  if !match writeFailure.outcome with | .error _ => true | .ok _ => false then
    throw (IO.userError "write-hook failure was ignored")
  if writeFailure.hooks.events != #["access", "access", "alloc-1", "read", "alloc-2", "write"] then
    throw (IO.userError "write-hook failure ran a later copy stage")
  let unchanged ← requireBytes writeFailure.memory destId (allocRange Size.ZERO (Size.ofBytes 4))
  if unchanged != #[0, 0, 0, 0] then
    throw (IO.userError "write-hook failure unexpectedly copied bytes")
  IO.println s!"write-failure {traceText writeFailure.hooks}"
