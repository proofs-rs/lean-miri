import Miri.ABI.RuntimeLayout

open Miri.ABI

private def defaultLayout := RuntimeTargetDataLayout.default
private def range (first last : Nat) : WrappingRange :=
  ⟨BitVec.ofNat 128 first, BitVec.ofNat 128 last⟩
private def boolScalar : Scalar :=
  .Initialized (value := .Int .I8 false) (validRange := range 0 1)
private def fullScalar : Scalar :=
  .Initialized (value := .Int .I8 false) (validRange := range 0 255)
private def unionScalar : Scalar := .Union (value := .Int .I8 false)

private def errorFlag {ε α : Type} (result : Except ε α) : String :=
  match result with
  | .ok _ => "false"
  | .error _ => "true"

private def alignBytesText (align : Align) : String :=
  match Align.bytes align with
  | .ok bytes => toString bytes
  | .error _ => "error"

private def numScalable (count : Nat) : String :=
  match NumScalableVectors.fromFieldCount count with
  | none => "None"
  | some value => s!"Some(NumScalableVectors({value.value}))"

private def lines : List String := Id.run do
  let d := defaultLayout
  let pair : BackendRepr :=
    .ScalarPair (a := boolScalar) (b := fullScalar) (bOffset := Size.ofBytes 1)
  let registerWidths := [Reg.i8, Reg.i64, Reg.f64, Reg.f128,
    Reg.opaqueVector (Size.ofBytes 3)]
  let pointer32Offset : RuntimeTargetDataLayout := {
    d with addressSpaceInfo := #[
      (⟨1⟩, ⟨Size.ofBytes 8, Align.EIGHT, Size.ofBytes 4, false⟩),
      (⟨2⟩, ⟨Size.ofBytes 8, Align.EIGHT, Size.ofBytes 3, false⟩)
    ]
  }
  let vectorAlign := d.rustVectorAlign (Size.ofBytes 3)
  let vectorAlignZero := d.rustVectorAlign (Size.ofBytes 0)
  let vectorAlignOverflow := d.rustVectorAlign (Size.ofBytes ((UInt64.shiftLeft 1 63) + 1))
  let ptrSize := (Primitive.Pointer AddressSpace.ZERO).size d
  let ptrAlign := (Primitive.Pointer AddressSpace.ZERO).defaultAlign d
  let addressSize := RuntimeTargetDataLayout.pointerSizeIn pointer32Offset ⟨1⟩
  let addressOffset := RuntimeTargetDataLayout.pointerOffsetIn pointer32Offset ⟨1⟩
  let unknownAddressSpace := RuntimeTargetDataLayout.pointerSizeIn pointer32Offset ⟨3⟩
  let offsetWidthError := RuntimeTargetDataLayout.ptrSizedIntegerIn pointer32Offset ⟨2⟩
  let signedNonScalarError := (BackendRepr.Memory (sized := true)).isSigned
  let integerI64Align := match Integer.align .I64 d with
    | .ok a => alignBytesText a.abi
    | .error _ => "error"
  let floatF64Align := match Float.align .F64 d with
    | .ok a => alignBytesText a.abi
    | .error _ => "error"
  let pointerSizeText := match ptrSize with
    | .ok size => toString size.bytes
    | .error _ => "error"
  let pointerAlignText := match ptrAlign with
    | .ok a => alignBytesText a.abi
    | .error _ => "error"
  let unionRangeText := match unionScalar.validRange d with
    | .ok r => toString r.start.toNat ++ ":" ++ toString r.«end».toNat
    | .error _ => "error"
  let backendPairAlign := match pair.scalarPlatformAlign d with
    | .ok (some a) => "Some(" ++ alignBytesText a ++ ")"
    | .ok none => "None"
    | .error _ => "error"
  let backendPairSize := match pair.scalarSize d with
    | .ok (some size) => toString size.bytes
    | .ok none => "None"
    | .error _ => "error"
  let vectorAlignText := match vectorAlign with
    | .ok a => alignBytesText a
    | .error _ => "error"
  let registerAlignText := String.intercalate "," (registerWidths.map fun reg =>
    match reg.align d with
    | .ok align => alignBytesText align
    | .error _ => "error")
  let registerWidthError := Reg.mk .Integer (Size.ofBytes 17) |>.align d
  let vectorAlignZeroText := match vectorAlignZero with
    | .ok a => alignBytesText a
    | .error _ => "error"
  let addressSizeText := match addressSize with
    | .ok size => toString size.bytes
    | .error _ => "error"
  let addressOffsetText := match addressOffset with
    | .ok size => toString size.bytes
    | .error _ => "error"
  return [
    s!"integer_sizes={(Integer.size .I8).bytes},{(Integer.size .I16).bytes},{(Integer.size .I32).bytes},{(Integer.size .I64).bytes},{(Integer.size .I128).bytes}",
    s!"integer_names={Integer.intTyStr .I64},{Integer.uintTyStr .I128}",
    s!"integer_attr_pointer={match Integer.fromAttr d (.Pointer false) with | .ok .I64 => "I64" | _ => "error"}",
    s!"integer_align_i64={integerI64Align}",
    s!"integer_fit={match Integer.fitSigned (-129) with | .I16 => "I16" | _ => "other"},{match Integer.fitSigned 2147483648 with | .I64 => "I64" | _ => "other"},{match Integer.fitUnsigned (BitVec.ofNat 128 (2^64)) with | .I128 => "I128" | _ => "other"}",
    s!"integer_for_align={match Integer.forAlign d ⟨2⟩ with | .ok (some .I32) => "Some(I32)" | _ => "other"}",
    s!"integer_approx_align={match Integer.approximateAlign d Align.EIGHT with | .ok .I64 => "I64" | _ => "other"}",
    s!"integer_from_size={match Integer.fromSize (Size.ofBytes 16) with | .ok .I128 => "Ok(I128)" | _ => "other"},{match Integer.fromSize (Size.ofBytes 3) with | .error (.unsupportedBitWidth 24) => "Err(\"rust does not support integers with 24 bits\")" | _ => "other"}",
    s!"float_info={(Float.size .PpcF128).bytes},{Float.tyStr .F16B},{floatF64Align}",
    s!"pointer_info={pointerSizeText},{pointerAlignText},Integer",
    s!"scalar_checks={boolScalar.isBool},{boolScalar.isSigned},{match fullScalar.isAlwaysValid d with | .ok b => b | .error _ => false},{unionScalar.isUninitValid}",
    s!"scalar_union_range={unionRangeText}",
    s!"backend_pair={backendPairAlign},{backendPairSize}",
    s!"backend_equiv={(BackendRepr.Scalar boolScalar).eqUpToValidity (BackendRepr.Scalar fullScalar)}",
    s!"backend_union_memory={match (BackendRepr.Memory (sized := false)).toUnion with | .Memory (sized := true) => true | _ => false}",
    s!"lane_count={errorFlag (BackendLaneCount.new 0)},{match BackendLaneCount.new 32768 with | .ok n => n.asU64 | .error _ => 0},{match BackendLaneCount.new 32768 with | .ok n => n.isPowerOfTwo | .error _ => false},{errorFlag (BackendLaneCount.new 32769)}",
    s!"scalable_fields={numScalable 2},{numScalable 7},{numScalable 8}",
    s!"vector_align={vectorAlignText}",
    s!"register_align={registerAlignText}",
    s!"register_width_error={errorFlag registerWidthError}",
    s!"vector_align_zero={vectorAlignZeroText}",
    s!"vector_align_overflow={errorFlag vectorAlignOverflow}",
    s!"address_space={addressSizeText},{addressOffsetText},I32",
    s!"unknown_address_space={errorFlag unknownAddressSpace}",
    s!"offset_width_error={errorFlag offsetWidthError}",
    s!"signed_non_scalar_error={errorFlag signedNonScalarError}"
  ]

def main : IO Unit := do
  for line in lines do
    IO.println line
