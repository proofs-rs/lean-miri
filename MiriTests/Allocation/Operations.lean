import Miri.Memory.Allocation

open Miri.ABI
open Miri.Memory

private def size (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def range (start finish : Nat) : AllocRange :=
  allocRange (size start) (size (finish - start))

private def requireOk {α : Type} (label : String) (result : Except AllocError α) : IO α := do
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError s!"{label}: {reason}")

private def runMutation (label : String)
    (action : EStateM AllocError (Allocation CtfeProvenance Unit) Unit)
    (allocation : Allocation CtfeProvenance Unit) : IO (Allocation CtfeProvenance Unit) := do
  match action allocation with
  | .ok () next => pure next
  | .error reason _ => throw (IO.userError s!"{label}: {reason}")

private def actualBytes (allocation : Allocation CtfeProvenance Unit) (count : Nat) :
    IO (Array UInt8) :=
  requireOk "raw allocation bytes" (allocation.getBytesUnchecked (range 0 count))

private def uninitAllocation (count : Nat) : IO (Allocation CtfeProvenance Unit) :=
  requireOk "uninitialized allocation"
    (Allocation.tryNew (Prov := CtfeProvenance) (size count) Align.ONE .Uninit
      (fun requested _ => some (Array.replicate requested.bytes.toNat 0)))

def main : IO Unit := do
  let source ← requireOk "copy source"
    (Allocation.fromBytes (Prov := CtfeProvenance) #[10, 20] Align.ONE .Not)
  let destination ← requireOk "copy destination"
    (Allocation.fromBytes (Prov := CtfeProvenance) (Array.replicate 6 0) Align.ONE .Mut)
  let repeated ← runMutation "repeated copy"
    (Allocation.copyRepeatedly source (range 0 2) (size 0) 3 (size 8) false true)
    destination
  let repeatedBytes ← actualBytes repeated 6
  if repeatedBytes != #[10, 20, 10, 20, 10, 20] then
    throw (IO.userError "repeated copy did not replicate the source byte range")
  match repeated.getBytesStripProvenance ⟨.little, .w64⟩ (range 0 6) with
  | .ok _ => pure ()
  | .error reason => throw (IO.userError s!"repeated copy did not initialize its destination: {reason}")

  let overlapping ← requireOk "overlap allocation"
    (Allocation.fromBytes (Prov := CtfeProvenance) #[1, 2, 3, 4] Align.ONE .Mut)
  let moved ← runMutation "overlapping single copy"
    (Allocation.copy overlapping (range 0 3) (size 1) (size 8) true false)
    overlapping
  let movedBytes ← actualBytes moved 4
  if movedBytes != #[1, 1, 2, 3] then
    throw (IO.userError "overlapping one-copy operation did not preserve memmove bytes")

  let allUninit ← uninitAllocation 2
  let sentinel ← requireOk "uninitialized-copy destination"
    (Allocation.fromBytes (Prov := CtfeProvenance) #[9, 8, 7, 6] Align.ONE .Mut)
  let untouched ← runMutation "all-uninitialized repeated copy"
    (Allocation.copyRepeatedly allUninit (range 0 2) (size 0) 2 (size 8) false true)
    sentinel
  let sentinelBytes ← actualBytes untouched 4
  if sentinelBytes != #[9, 8, 7, 6] then
    throw (IO.userError "all-uninitialized copy changed arbitrary destination byte storage")
  match untouched.getBytesStripProvenance ⟨.little, .w64⟩ (range 0 4) with
  | .error (.invalidUninitBytes (some _)) => pure ()
  | other => throw (IO.userError s!"all-uninitialized copy did not clear destination init bits: {other}")

  let uninitSelf ← uninitAllocation 6
  let repeatedUninitSelf ← runMutation "all-uninitialized repeated self-copy"
    (Allocation.copyRepeatedly uninitSelf (range 0 2) (size 1) 2 (size 8) true false)
    uninitSelf
  if (← actualBytes repeatedUninitSelf 6) != Array.replicate 6 0 then
    throw (IO.userError "all-uninitialized self-copy changed arbitrary destination bytes")

  let id ← match AllocId.ofUInt64 7 with
    | some id => pure id
    | none => throw (IO.userError "test allocation ID 7 was rejected")
  let provenance ← match CtfeProvenance.fromAllocId id with
    | .ok provenance => pure provenance
    | .error _ => throw (IO.userError "test provenance construction failed")
  let pointerAllocation ← uninitAllocation 16
  let pointerAllocation ← runMutation "pointer setup"
    (Allocation.writePointer ⟨.little, .w64⟩ (range 0 8)
      (Pointer.new provenance (size 0x1234))) pointerAllocation
  let overlapResult := Allocation.copy pointerAllocation (range 0 8) (size 4) (size 8) true true
      pointerAllocation
  match overlapResult with
  | .error .copyRangesOverlap next =>
    if !next.provenanceMap.byteFragments.isSome || !next.provenanceMap.ptrs.isEmpty then
      throw (IO.userError "copy overlap failure did not preserve the preceding provenance clear")
  | .error reason _ => throw (IO.userError s!"wrong overlap error: {reason}")
  | .ok () _ => throw (IO.userError "overlapping nonoverlapping-copy request succeeded")

  let adjustHooks : Array String := #[]
  let allocationCallback : Array UInt8 → Align → Array String →
      EStateM.Result String (Array String) (Array UInt8) :=
    fun bytes _ state => .ok bytes (state.push "bytes")
  let pointerFailure : Pointer CtfeProvenance → Array String →
      EStateM.Result String (Array String) (Pointer CtfeProvenance) :=
    fun pointer state =>
      .error "pointer conversion failed"
        (state.push s!"pointer:{pointer.offset.bytes.toNat}")
  match Allocation.adjustFromTcx pointerAllocation ⟨.little, .w64⟩
      allocationCallback pointerFailure adjustHooks with
  | .error (.pointerAdjustment "pointer conversion failed") events =>
    if events != #["bytes", "pointer:4660"] then
      throw (IO.userError s!"pointer-adjustment error lost callback order/state: {events}")
  | .error reason events =>
    throw (IO.userError s!"wrong pointer-adjustment failure {repr reason}: {events}")
  | .ok _ _ => throw (IO.userError "failed pointer adjustment returned an allocation")

  let byteFailure : Array UInt8 → Align → Array String →
      EStateM.Result String (Array String) (Array UInt8) :=
    fun _ _ state => .error "byte backend failed" (state.push "bytes-failed")
  let unreachablePointer : Pointer CtfeProvenance → Array String →
      EStateM.Result String (Array String) (Pointer CtfeProvenance) :=
    fun _ state => .error "pointer callback ran after byte failure" (state.push "pointer")
  match Allocation.adjustFromTcx pointerAllocation ⟨.little, .w64⟩
      byteFailure unreachablePointer adjustHooks with
  | .error (.byteConversion "byte backend failed") events =>
    if events != #["bytes-failed"] then
      throw (IO.userError s!"byte-conversion error ran later callbacks or lost state: {events}")
  | .error reason events =>
    throw (IO.userError s!"wrong byte-conversion failure {repr reason}: {events}")
  | .ok _ _ => throw (IO.userError "failed byte conversion returned an allocation")

  IO.println "allocation byte, uninit, repeated-copy, and adjustment transitions passed"
