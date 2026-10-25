import Miri.Interpreter.Aggregate
open Miri.Interpreter

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
  let some sourceId := AllocId.ofUInt64 1 | throw (IO.userError "source id")
  let some destId := AllocId.ofUInt64 2 | throw (IO.userError "dest id")
  let action := aggregateMemoryCopyRepeatedly (Size.ofBytes 8) copyHooks
    (fun s : MemoryState Provenance Unit Unit × CopyTrace => s.1) Prod.snd
    (fun _ memory hooks => (memory, hooks))
    (fun error => StepError.callback s!"{error}")
    (ptr sourceId) (ptr destId) (Size.ofBytes 2) 2 true
  match action (memory, {}) with
  | .error error _ => throw (IO.userError s!"aggregate adapter failed: {repr error}")
  | .ok () state =>
    let bytes ← requireBytes state.1 destId (allocRange Size.ZERO (Size.ofBytes 4))
    unless bytes == #[10, 20, 10, 20] do throw (IO.userError "aggregate repeated bytes")
    unless state.2.events == #["access", "access", "alloc-1", "read", "alloc-2", "write"] do
      throw (IO.userError "aggregate memory hook order")
  match action (memory, { fail := "write" }) with
  | .ok _ _ => throw (IO.userError "write failure succeeded")
  | .error _ state =>
    unless state.2.events == #["access", "access", "alloc-1", "read", "alloc-2", "write"] do
      throw (IO.userError "error lost effects")
  IO.println "aggregate repeated-copy memory adapter passed"
