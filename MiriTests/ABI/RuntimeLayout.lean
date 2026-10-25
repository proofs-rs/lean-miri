import Miri.ABI.RuntimeLayout

open Miri.ABI

private def layout : RuntimeTargetDataLayout := RuntimeTargetDataLayout.default
private def range (first last : Nat) : WrappingRange :=
  ⟨BitVec.ofNat 128 first, BitVec.ofNat 128 last⟩
private def boolScalar : Scalar :=
  .Initialized (value := .Int .I8 false) (validRange := range 0 1)
private def fullByteScalar : Scalar :=
  .Initialized (value := .Int .I8 false) (validRange := range 0 255)
private def unionByteScalar : Scalar := .Union (value := .Int .I8 false)

example : RuntimeTargetDataLayout.validate layout = .ok () := by decide +kernel
example : layout.objSizeBound = 2305843009213693952 := by decide
example : layout.pointerSize = Size.ofBytes 8 := by decide
example : layout.pointerOffset = Size.ofBytes 8 := by decide
example : layout.pointerAlign = .ok (AbiAlign.new Align.EIGHT) := by decide

example : Integer.size .I8 = Size.ofBytes 1 := by decide
example : Integer.size .I128 = Size.ofBytes 16 := by decide
example : Integer.intTyStr .I64 = "i64" := by decide
example : Integer.uintTyStr .I128 = "u128" := by decide
example : Integer.fromAttr layout (.Pointer true) = .ok .I64 := by decide
example : Integer.fromAttr layout (.Fixed .I16 false) = .ok .I16 := by decide
example : (IntegerType.Pointer true).isSigned := by decide
example : (IntegerType.Fixed .I16 false).isSigned = false := by decide
example : (Integer.align .I64 layout).map (·.abi) = .ok ⟨2⟩ := by decide
example : Integer.signedMax .I128 = 170141183460469231731687303715884105727 := by decide
example : Integer.signedMin .I128 = -170141183460469231731687303715884105728 := by decide
example : Integer.signedMax .I8 = 127 := by decide
example : Integer.signedMin .I8 = -128 := by decide
example : Integer.fitSigned (-129) = .I16 := by decide
example : Integer.fitSigned 2147483648 = .I64 := by decide
example : Integer.fitUnsigned (BitVec.ofNat 128 18446744073709551616) = .I128 := by decide
example : Integer.forAlign layout ⟨2⟩ = .ok (some .I32) := by decide
example : Integer.approximateAlign layout Align.EIGHT = .ok .I64 := by decide
example : Integer.fromSize (Size.ofBytes 16) = .ok .I128 := by decide
example : Integer.fromSize (Size.ofBytes 3) = .error (.unsupportedBitWidth 24) := by decide

example : Float.size .PpcF128 = Size.ofBytes 16 := by decide
example : Float.size .F16B = Size.ofBytes 2 := by decide
example : Float.size .F32 = Size.ofBytes 4 := by decide
example : Float.size .F64 = Size.ofBytes 8 := by decide
example : Float.tyStr .F16B = "f16b" := by decide
example : (Float.align .F64 layout).map (·.abi) = .ok Align.EIGHT := by decide

example : (Primitive.Pointer AddressSpace.ZERO).size layout = .ok (Size.ofBytes 8) := by decide
example : (Primitive.Pointer AddressSpace.GPU_CONSTANT).size layout =
    .error (.unknownAddressSpace AddressSpace.GPU_CONSTANT) := by decide
example : (Primitive.Pointer AddressSpace.ZERO).regKind = .Integer := by decide
example : (RegKind.fromPrimitive (.Float .PpcF128)) = .PpcF128 := by decide
example : (Primitive.Int .I32 true).size layout = .ok (Size.ofBytes 4) := by decide
example : (Primitive.Float .F16).defaultAlign layout = .ok (AbiAlign.new ⟨1⟩) := by decide
example : (Scalar.size fullByteScalar layout) = .ok (Size.ofBytes 1) := by decide
example : (Scalar.defaultAlign fullByteScalar layout) = .ok (AbiAlign.new Align.ONE) := by decide

example : boolScalar.isBool := by decide
example : boolScalar.isSigned = false := by decide
example : fullByteScalar.isAlwaysValid layout = .ok true := by decide
example : boolScalar.isAlwaysValid layout = .ok false := by decide
example : unionByteScalar.isUninitValid := by decide
example : unionByteScalar.validRange layout = .ok (range 0 255) := by decide
example : unionByteScalar.setValidRange (range 0 1) =
    .error .cannotChangeUnionValidRange := by decide
example : boolScalar.toUnion = unionByteScalar := by decide

private def pairRepr : BackendRepr :=
  .ScalarPair (a := boolScalar) (b := fullByteScalar) (bOffset := Size.ofBytes 1)

example : pairRepr.scalarPlatformAlign layout = .ok (some Align.ONE) := by decide
example : pairRepr.scalarSize layout = .ok (some (Size.ofBytes 2)) := by decide
example : (BackendRepr.ScalarPair (a := boolScalar) (b := fullByteScalar)
    (bOffset := Size.ofBytes 18446744073709551615)).scalarSize layout =
    .error (.size (.u64Overflow "add" 18446744073709551615 1)) := by decide
private def alignOverflowPair : BackendRepr :=
  .ScalarPair (a := boolScalar)
    (b := .Union (value := .Int .I32 false))
    (bOffset := Size.ofBytes 18446744073709551611)
example : alignOverflowPair.scalarSize layout =
    .error (.alignment (.sizeOverflow (Size.ofBytes 18446744073709551615) 3)) := by decide
example : (BackendRepr.Scalar fullByteScalar).scalarSize layout =
    .ok (some (Size.ofBytes 1)) := by decide
example : (BackendRepr.Memory (sized := false)).isSized = false := by decide
example : (BackendRepr.Scalar fullByteScalar).isScalar := by decide
example (count : BackendLaneCount) :
    (BackendRepr.SimdVector (element := fullByteScalar) (count := count)).isScalarOrSimd =
    true := by rfl
example : pairRepr.toUnion =
    .ScalarPair (a := unionByteScalar) (b := unionByteScalar) (bOffset := Size.ofBytes 1) := by decide
example : (BackendRepr.Scalar (.Union (value := .Int .I8 false))).isBool = false := by decide
example : (BackendRepr.Memory (sized := false)).isUnsized := by decide
example : (BackendRepr.Memory (sized := false)).toUnion =
    BackendRepr.Memory (sized := true) := by decide
example : (BackendRepr.Scalar boolScalar).eqUpToValidity
    (BackendRepr.Scalar fullByteScalar) := by decide
example : pairRepr.isSigned = .error .isSignedOnNonScalar := by decide

example : BackendLaneCount.new 0 = .error .zeroLength := by decide
example : (BackendLaneCount.new 32768).map BackendLaneCount.asU64 = .ok 32768 := by decide
example : BackendLaneCount.new 32769 = .error (.oversized 32768) := by decide
example : (BackendLaneCount.new 32768).map BackendLaneCount.isPowerOfTwo = .ok true := by decide
example : NumScalableVectors.fromFieldCount 2 = some ⟨2⟩ := by decide
example : NumScalableVectors.fromFieldCount 7 = some ⟨7⟩ := by decide
example : NumScalableVectors.fromFieldCount 8 = none := by decide
example : Reg.i8.align layout = .ok Align.ONE := by decide
example : Reg.i64.align layout = .ok ⟨2⟩ := by decide
example : Reg.f64.align layout = .ok Align.EIGHT := by decide
example : Reg.f128.align layout = .ok ⟨4⟩ := by decide
example : (Reg.opaqueVector (Size.ofBytes 3)).align layout = .ok ⟨2⟩ := by decide +kernel
example : (Reg.mk .PpcF128 (Size.ofBytes 18446744073709551615)).align layout =
    .ok ⟨4⟩ := by decide
example : (Reg.mk .Integer (Size.ofBytes 17)).align layout =
    .error (.unsupportedIntegerWidth 136) := by decide
example : (Reg.mk .Float (Size.ofBytes 3)).align layout =
    .error (.unsupportedFloatWidth 24) := by decide

private def pointer32OffsetLayout : RuntimeTargetDataLayout := {
  layout with
  addressSpaceInfo := #[
    (⟨1⟩, ⟨Size.ofBytes 8, Align.EIGHT, Size.ofBytes 4, false⟩)
  ]
}

example : RuntimeTargetDataLayout.ptrSizedIntegerIn pointer32OffsetLayout ⟨1⟩ = .ok .I32 := by decide
example : RuntimeTargetDataLayout.pointerSizeIn pointer32OffsetLayout ⟨1⟩ = .ok (Size.ofBytes 8) := by decide
example : RuntimeTargetDataLayout.ptrSizedIntegerIn layout AddressSpace.ZERO = .ok .I64 := by decide
example : RuntimeTargetDataLayout.rustVectorAlign layout (Size.ofBytes 3) =
    .ok (Align.mk 2) := by decide +kernel
example : RuntimeTargetDataLayout.rustVectorAlign layout (Size.ofBytes 0) =
    .ok Align.ONE := by decide
example : RuntimeTargetDataLayout.rustVectorAlign layout
    (Size.ofBytes ((UInt64.shiftLeft 1 63) + 1)) =
    .error (.vectorAlignmentOverflow (Size.ofBytes ((UInt64.shiftLeft 1 63) + 1))) := by decide

private def inconsistentLayout : RuntimeTargetDataLayout := {
  layout with base := { layout.base with pointerWidth := .w32 }
}

example : RuntimeTargetDataLayout.validate inconsistentLayout =
    .error (.targetPointerWidthMismatch .w32 (Size.ofBytes 8)) := by decide +kernel

private def missingInstructionSpace : RuntimeTargetDataLayout := {
  layout with instructionAddressSpace := ⟨1⟩
}

example : RuntimeTargetDataLayout.validate missingInstructionSpace =
    .error (.missingInstructionAddressSpace ⟨1⟩) := by decide +kernel

private def duplicateVectorSize : RuntimeTargetDataLayout := {
  layout with vectorAlign := #[
    (Size.ofBytes 8, Align.EIGHT),
    (Size.ofBytes 8, Align.ONE)
  ]
}

example : RuntimeTargetDataLayout.validate duplicateVectorSize =
    .error (.duplicateVectorSize (Size.ofBytes 8)) := by decide +kernel
