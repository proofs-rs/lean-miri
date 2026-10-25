import Miri.Memory.Access

open Miri.ABI
open Miri.Memory

private def size (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)

private def requireFailure (label : String) (expected : AllocError)
    (result : Except AllocError α) : IO Unit := do
  match result with
  | .error actual =>
    if actual != expected then
      throw (IO.userError s!"{label}: expected {expected}, got {actual}")
  | .ok _ => throw (IO.userError s!"{label}: invalid input returned an allocation/result")

def main : IO Unit := do
  requireFailure "host exhaustion" .hostMemoryExhausted
    (Allocation.tryNew (Prov := CtfeProvenance) (size 2) Align.ONE .Zero
      (fun _ _ => none))
  requireFailure "storage length mismatch" (.storageLengthMismatch (size 2) 1)
    (Allocation.tryNew (Prov := CtfeProvenance) (size 2) Align.ONE .Zero
      (fun _ _ => some #[0]))
  requireFailure "zeroed-storage contract" (.storageBackendNotZeroed 1 1)
    (Allocation.tryNew (Prov := CtfeProvenance) (size 2) Align.ONE .Zero
      (fun _ _ => some #[0, 1]))
  requireFailure "unrepresentable alignment" (.alignment (.shiftOverflow 64))
    (Allocation.fromBytes (Prov := CtfeProvenance) #[1] ⟨64⟩ .Not)

  let allocation ← match Allocation.fromBytes (Prov := CtfeProvenance) #[4, 2] Align.ONE .Not with
    | .ok allocation => pure allocation
    | .error reason => throw (IO.userError s!"fromBytes unexpectedly failed: {reason}")
  requireFailure "raw-slice bounds" (.outOfBounds (allocRange (size 1) (size 2)) (size 2))
    (allocation.getBytesUnchecked (allocRange (size 1) (size 2)))
  match allocation.inspectWithUninitAndPtrOutsideInterpreter 2 1 with
  | .error (.invalidSliceEndpoints 2 1 2) => pure ()
  | other => throw (IO.userError s!"invalid raw endpoints were not preserved: {other}")

  if Allocation.byteSize allocation != size 2 then
    throw (IO.userError "allocation metadata size differs from its backing byte length")

  let id ← match AllocId.ofUInt64 1 with
    | some id => pure id
    | none => throw (IO.userError "test allocation ID 1 was rejected")
  let invalidAlignResult : Except AccessError (Option Misalignment) :=
    isPtrMisaligned (ProvExtra := Unit)
      (Pointer.withoutProvenance (Prov := CtfeProvenance) 3) ⟨30⟩ false
      (fun _ _ => .error 3)
      (fun _ => .error (.unavailable id))
      (fun _ _ _ _ _ => none)
  match invalidAlignResult with
  | .error (.malformedAlignment (.tooLarge bytes)) =>
    if bytes != 1073741824 then throw (IO.userError "invalid alignment error reported the wrong size")
  | _ => throw (IO.userError "invalid source alignment was not rejected")

  let highPointer : Pointer (Option CtfeProvenance) :=
    Pointer.withoutProvenance (UInt64.ofNat 18446744073709551615)
  let highResolution : PointerResolver CtfeProvenance Unit :=
    fun _ _ => .ok ⟨id, Size.ofBytes (UInt64.ofNat 18446744073709551615), ()⟩
  let liveLookup : LiveAllocationLookup :=
    fun _ => .ok ⟨size 8, Align.ONE, .liveData, .Mut⟩
  let unsupportedTarget : PointerArithmetic := ⟨size 16⟩
  match checkAndDerefPtr unsupportedTarget highPointer 1 .memoryAccess highResolution liveLookup with
  | .error (.pointerArithmetic .signedConversionOverflow) => pure ()
  | _ => throw (IO.userError "target isize conversion failure was not preserved")
