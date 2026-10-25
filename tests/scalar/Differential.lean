import Miri.Memory.Allocation

open Miri.ABI
open Miri.Memory

private def size (bytes : Nat) : Size := Size.ofBytes (UInt64.ofNat bytes)
private def range (start finish : Nat) : AllocRange := allocRange (size start) (size (finish - start))
private def bits (value : Nat) : U128 := BitVec.ofNat 128 value

private def showInt (value : ScalarInt) : String :=
  s!"{value.size.bytes.toNat}:{value.data.toNat}"

private def emitUInt (tag : String) (value : Nat) (bytes : Nat) : IO Unit := do
  match ScalarInt.tryFromUInt (bits value) (size bytes) with
  | .ok (some scalar) => IO.println s!"U {tag} {showInt scalar}"
  | .ok none => IO.println s!"U {tag} -"
  | .error reason => throw (IO.userError s!"unexpected unsigned construction error: {reason}")

private def emitTruncatedUInt (tag : String) (value : Nat) (bytes : Nat) : IO Unit := do
  match ScalarInt.truncateFromUInt (bits value) (size bytes) with
  | .ok (scalar, overflow) => IO.println s!"T {tag} {showInt scalar} {overflow}"
  | .error reason => throw (IO.userError s!"unexpected unsigned truncation error: {reason}")

private def emitInt (tag : String) (value : Int) (bytes : Nat) : IO Unit := do
  match ScalarInt.tryFromInt value (size bytes) with
  | .ok (some scalar) => IO.println s!"I {tag} {showInt scalar}"
  | .ok none => IO.println s!"I {tag} -"
  | .error reason => throw (IO.userError s!"unexpected signed construction error: {reason}")

private def emitTruncatedInt (tag : String) (value : Int) (bytes : Nat) : IO Unit := do
  match ScalarInt.truncateFromInt value (size bytes) with
  | .ok (scalar, overflow) => IO.println s!"J {tag} {showInt scalar} {overflow}"
  | .error reason => throw (IO.userError s!"unexpected signed truncation error: {reason}")

private def requireScalar {Prov : Type} (label : String)
    (result : Except ScalarError (Scalar Prov)) : IO (Scalar Prov) := do
  match result with
  | .ok scalar => pure scalar
  | .error reason => throw (IO.userError s!"{label}: {reason}")

private def showScalar (layout : TargetDataLayout) (value : Scalar CtfeProvenance) :
    IO String := do
  if value.isPointer then
    let pointer ← match value.toPointer layout with
      | .ok pointer => pure pointer
      | .error reason => throw (IO.userError s!"pointer scalar decode failed: {reason}")
    match pointer.provenance with
    | some provenance =>
      return s!"P:{value.size.bytes.toNat}:{pointer.offset.bytes.toNat}:{provenance.allocId.value.toNat}"
    | none => return s!"P:{value.size.bytes.toNat}:{pointer.offset.bytes.toNat}:0"
  let int ← match value.toScalarInt with
    | .ok int => pure int
    | .error reason => throw (IO.userError s!"integer scalar decode failed: {reason}")
  return s!"I:{showInt int}"

inductive AddressProvenance where
  | address
  deriving DecidableEq, Repr

instance : PointerProvenance AddressProvenance where
  offsetIsAddr := true
  wildcard := none
  getAllocId := fun _ => none

def main : IO Unit := do
  for (tag, value, bytes) in #[
      ("zero8", 0, 1), ("one8", 1, 1), ("max8", 255, 1),
      ("overflow8", 256, 1), ("max16", 2^128 - 1, 16),
      ("wideTruncate", 0x123456789abcdef0, 4)] do
    emitUInt tag value bytes
  emitTruncatedUInt "wide" 0x123456789abcdef0 4
  emitTruncatedUInt "maxTo16" (2^128 - 1) 16

  for (tag, value, bytes) in #[
      ("minusOne8", -1, 1), ("min8", -128, 1), ("under8", -129, 1),
      ("min128", -(2^127), 16), ("max128", 2^127 - 1, 16)] do
    emitInt tag value bytes
  emitTruncatedInt "minus129" (-129) 1
  emitTruncatedInt "plus255" 255 1

  match ScalarInt.tryToBool ScalarInt.trueValue with
  | .ok value => IO.println s!"Q bool_true {value}"
  | .error reason => throw (IO.userError s!"true bool conversion failed: {reason}")
  let invalidBool ← match ScalarInt.tryFromUInt (bits 2) (size 1) with
    | .ok (some scalar) => pure scalar
    | _ => throw (IO.userError "could not construct invalid bool test scalar")
  IO.println s!"Q bool_invalid {(match invalidBool.tryToBool with | .error _ => true | .ok _ => false)}"
  for (tag, code) in [("letter", 65), ("surrogate", 0xd800), ("pastUnicode", 0x110000)] do
    let scalar ← match ScalarInt.tryFromUInt (bits code) (size 4) with
      | .ok (some scalar) => pure scalar
      | _ => throw (IO.userError "could not construct char test scalar")
    match scalar.toChar with
    | .ok char => IO.println s!"C {tag} {char.toNat}"
    | .error (.invalidChar _) => IO.println s!"C {tag} -"
    | .error reason => throw (IO.userError s!"unexpected char conversion error: {reason}")

  let ordering ← match ScalarInt.tryFromUInt (bits 3) (size 4) with
    | .ok (some scalar) =>
      match scalar.toAtomicOrdering with
      | .ok value => pure value
      | .error reason => throw (IO.userError s!"atomic-ordering conversion failed: {reason}")
    | _ => throw (IO.userError "could not construct atomic-ordering scalar")
  let orderingCode := match ordering with
    | .relaxed => 0 | .release => 1 | .acquire => 2 | .acqRel => 3 | .seqCst => 4
  IO.println s!"E atomic {orderingCode}"
  let simd ← match ScalarInt.tryFromUInt (bits 2) (size 4) with
    | .ok (some scalar) =>
      match scalar.toSimdAlignment with
      | .ok value => pure value
      | .error reason => throw (IO.userError s!"SIMD-alignment conversion failed: {reason}")
    | _ => throw (IO.userError "could not construct SIMD-alignment scalar")
  let simdCode := match simd with
    | .unaligned => 0 | .element => 1 | .vector => 2
  IO.println s!"E simd {simdCode}"
  let mismatch := ScalarInt.trueValue.toBits (size 2)
  IO.println s!"P mismatch {(match mismatch with | .error _ => true | .ok _ => false)}"
  IO.println s!"P zero_size {(match ScalarInt.null (size 0) with | .error _ => true | .ok _ => false)}"

  let layout : TargetDataLayout := ⟨.big, .w64⟩
  let scalar : Scalar CtfeProvenance ←
    requireScalar "from_uint" (Scalar.fromUInt (bits 0x1234) (size 2))
  let scalarBits ← match scalar.toUInt (size 2) with
    | .ok value => pure value.toNat
    | .error reason => throw (IO.userError s!"from_uint read failed: {reason}")
  IO.println s!"S from_uint {scalar.size.bytes.toNat} {scalarBits}"
  let signed : Scalar CtfeProvenance ←
    requireScalar "from_int" (Scalar.fromInt (-129) (size 2))
  match signed.toInt (size 2) with
  | .ok value => IO.println s!"S signed {value}"
  | .error reason => throw (IO.userError s!"signed scalar read failed: {reason}")
  match (Scalar.fromBool true : Scalar CtfeProvenance).toBool with
  | .ok value => IO.println s!"S bool {value}"
  | .error reason => throw (IO.userError s!"bool scalar read failed: {reason}")
  match (Scalar.fromChar 'A' : Scalar CtfeProvenance).toChar with
  | .ok value => IO.println s!"S char {value.toNat}"
  | .error reason => throw (IO.userError s!"char scalar read failed: {reason}")

  let id ← match AllocId.ofUInt64 1 with
    | some id => pure id
    | none => throw (IO.userError "test allocation ID 1 was rejected")
  let provenance ← match CtfeProvenance.fromAllocId id with
    | .ok provenance => pure provenance
    | .error _ => throw (IO.userError "test CTFE provenance could not be constructed")
  let pointerScalar := Scalar.fromPointer layout (Pointer.new provenance (size 0x1234))
  let relCast := pointerScalar.tryToScalarInt
  IO.println s!"S rel_cast {(match relCast with | .ok (.erasedPointer _ _) => true | _ => false)}"
  IO.println s!"S rel_read_bits {(match pointerScalar.toBits (size 8) with | .error .readPointerAsInt => true | _ => false)}"

  let addressScalar := Scalar.fromPointer layout (Pointer.new AddressProvenance.address (size 0x1234))
  match addressScalar.tryToScalarInt with
  | .ok (.integer int) => IO.println s!"S addr_cast {showInt int}"
  | _ => throw (IO.userError "address provenance did not expose its absolute address")
  let intPointer : Scalar CtfeProvenance ←
    requireScalar "to_pointer" (Scalar.fromUInt (bits 0x1234) (size 8))
  match intPointer.toPointer layout with
  | .ok pointer => IO.println s!"S to_pointer {pointer.provenance.isNone} {pointer.offset.bytes.toNat}"
  | .error reason => throw (IO.userError s!"integer-to-pointer conversion failed: {reason}")
  let optionalRelative : Pointer (Option CtfeProvenance) :=
    ⟨size 0x1234, some provenance⟩
  let optionalRelativeScalar ← requireScalar "from maybe relative pointer"
    (Scalar.fromMaybePointer layout optionalRelative)
  IO.println s!"S maybe_relative {← showScalar layout optionalRelativeScalar}"
  let optionalInteger : Pointer (Option CtfeProvenance) :=
    Pointer.withoutProvenance (UInt64.ofNat 0x1234)
  let optionalIntegerScalar ← requireScalar "from maybe integer pointer"
    (Scalar.fromMaybePointer layout optionalInteger)
  IO.println s!"S maybe_integer {← showScalar layout optionalIntegerScalar}"
  let roundtripPointer ← match pointerScalar.toPointer layout with
    | .ok pointer => pure pointer
    | .error reason => throw (IO.userError s!"relative pointer round trip failed: {reason}")
  IO.println s!"S to_pointer_relative {roundtripPointer.provenance.isSome} {roundtripPointer.offset.bytes.toNat}"

  let mut initialized ← match Allocation.tryNew (Prov := CtfeProvenance) (size 4) Align.ONE .Zero
      (fun requested _ => some (Array.replicate requested.bytes.toNat 0)) with
    | .ok allocation => pure allocation
    | .error reason => throw (IO.userError s!"integer allocation creation failed: {reason}")
  let integerScalar ← requireScalar "integer scalar" (Scalar.fromUInt (bits 0x12345678) (size 4))
  match Allocation.writeScalar layout (range 0 4)
      integerScalar initialized with
  | .error reason _ => throw (IO.userError s!"integer scalar write failed: {reason}")
  | .ok () allocation => initialized := allocation
  match initialized.readScalar layout (range 0 4) false with
  | .ok value => IO.println s!"A int {← showScalar layout value}"
  | .error reason => throw (IO.userError s!"integer scalar read failed: {reason}")

  let mut pointerAllocation ← match Allocation.tryNew (Prov := CtfeProvenance) (size 8) Align.ONE .Uninit
      (fun requested _ => some (Array.replicate requested.bytes.toNat 0)) with
    | .ok allocation => pure allocation
    | .error reason => throw (IO.userError s!"pointer allocation creation failed: {reason}")
  match Allocation.writeScalar layout (range 0 8) pointerScalar pointerAllocation with
  | .error reason _ => throw (IO.userError s!"pointer scalar write failed: {reason}")
  | .ok () allocation => pointerAllocation := allocation
  match pointerAllocation.readScalar layout (range 0 8) true with
  | .ok value => IO.println s!"A pointer {← showScalar layout value}"
  | .error reason => throw (IO.userError s!"pointer scalar read failed: {reason}")
  let pointerAsInt := pointerAllocation.readScalar layout (range 0 8) false
  IO.println s!"A pointer_as_int {(match pointerAsInt with | .error (.readPointerAsInt none) => true | _ => false)}"
  let uninit ← match Allocation.tryNew (Prov := CtfeProvenance) (size 2) Align.ONE .Uninit
      (fun requested _ => some (Array.replicate requested.bytes.toNat 0)) with
    | .ok allocation => pure allocation
    | .error reason => throw (IO.userError s!"uninitialized allocation creation failed: {reason}")
  IO.println s!"A uninit {(match uninit.readScalar layout (range 0 1) false with | .error (.invalidUninitBytes (some _)) => true | _ => false)}"
