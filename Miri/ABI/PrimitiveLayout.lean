import Miri.ABI.Layout

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd:
`rustc_ty_utils/src/layout.rs::layout_of_uncached` basic scalar branches, and
`rustc_abi/src/layout/simple.rs::{scalar,never_type}`. Recipes are source TyKind
constructors; all size, alignment, range, niche and seed results are computed
here for the selected target. Other layout constructors remain separate. -/
namespace Miri.ABI.PrimitiveLayout

private def rotateRight16 (value : UInt64) : UInt64 :=
  (value >>> 16) ||| (value <<< 48)

/-- The complete scalar constructor, including the source's layout randomization
seed. A full valid range has no niche; otherwise the exact range is retained. -/
def scalar (target : RuntimeTargetDataLayout) (value : Primitive)
    (range : WrappingRange) : Except String LayoutData := do
  let size ← value.size target |>.mapError toString
  let align ← value.defaultAlign target |>.mapError toString
  let full ← range.isFullFor size |>.mapError reprStr
  let kind : UInt64 := match value with
    | .Int _ true => 1 | .Int _ false => 2 | .Float _ => 3 | .Pointer _ => 4
  let seed := size.bytes + (kind <<< 32) + rotateRight16 (UInt64.ofNat range.start.toNat) +
    rotateRight16 (UInt64.ofNat range.end.toNat)
  return {
    fields := .Primitive, variants := .Single 0,
    backendRepr := .Scalar (.Initialized (value := value) (validRange := range)),
    largestNiche := if full then none else some ⟨Size.ZERO, value, range⟩,
    uninhabited := false, align, size, maxReprAlign := none,
    unadjustedAbiAlign := align.abi, reprC := false, randomizationSeed := seed }

private def integer (target : RuntimeTargetDataLayout) (recipe : String) :
    Except String (Option Primitive) := do
  let signed := recipe.startsWith "i"
  let kind ← match recipe with
    | "i8" | "u8" => pure (some Integer.I8)
    | "i16" | "u16" => pure (some .I16)
    | "i32" | "u32" => pure (some .I32)
    | "i64" | "u64" => pure (some .I64)
    | "i128" | "u128" => pure (some .I128)
    | "isize" | "usize" =>
      match target.defaultAddressSpacePointerSpec.pointerSize.bytes with
      | 2 => pure (some .I16) | 4 => pure (some .I32) | 8 => pure (some .I64)
      | _ => throw "unsupported target pointer-sized integer"
    | _ => pure none
  return kind.map fun kind => .Int kind signed

def compute (target : RuntimeTargetDataLayout) (recipe : String) : Except String LayoutData := do
  if recipe == "never" then
    return {
      fields := .Primitive, variants := .Empty, backendRepr := .Memory (sized := true),
      largestNiche := none, uninhabited := true, align := .new target.i8Align,
      size := Size.ZERO, maxReprAlign := none, unadjustedAbiAlign := target.i8Align,
      reprC := false, randomizationSeed := 0 }
  if recipe == "bool" then return ← scalar target (.Int .I8 false) ⟨0,1⟩
  if recipe == "char" then return ← scalar target (.Int .I32 false) ⟨0,0x10ffff⟩
  let value ← match ← integer target recipe with
    | some value => pure value
    | none => match recipe with
      | "f16" => pure (.Float .F16) | "f32" => pure (.Float .F32)
      | "f64" => pure (.Float .F64) | "f128" => pure (.Float .F128)
      | "fn_pointer" => pure (.Pointer target.instructionAddressSpace)
      | "raw_pointer" => pure (.Pointer .ZERO)
      | _ => throw "unknown primitive layout recipe"
  let size ← value.size target |>.mapError toString
  let range ← WrappingRange.full size |>.mapError reprStr
  let range := if recipe == "fn_pointer" then {range with start := 1} else range
  scalar target value range

/-- rustc_abi LayoutData::scalar_pair, including source tie-breaking for niches. -/
def scalarPair (target : RuntimeTargetDataLayout) (a b : Scalar) : Except String LayoutData := do
  let aSize ← a.size target |>.mapError reprStr
  let bSize ← b.size target |>.mapError reprStr
  let aAlign ← a.defaultAlign target |>.mapError reprStr
  let bAlign ← b.defaultAlign target |>.mapError reprStr
  let align := aAlign.abi.max bAlign.abi |>.max target.aggregateAlign
  let bOffset ← aSize.alignTo bAlign.abi |>.mapError toString
  let size ← (← bOffset.add bSize |>.mapError toString).alignTo align |>.mapError toString
  let niche (value : Scalar) (offset : Size) : Except String (Option (Niche × Nat)) := do
    match value with
    | .Union => return none
    | .Initialized (value := primitive) (validRange := range) =>
      let size ← primitive.size target |>.mapError toString
      let maximum ← size.unsignedIntMax |>.mapError toString
      let available := ((range.start - (range.end + 1)) &&& maximum).toNat
      return if available == 0 then none else some (⟨offset,primitive,range⟩,available)
  let an ← niche a Size.ZERO
  let bn ← niche b bOffset
  let largestNiche := match an,bn with
    | some (a,ac),some (b,bc) => some (if ac >= bc then a else b)
    | some (a,_),none => some a | none,some (b,_) => some b | none,none => none
  return {
    fields := .Arbitrary #[Size.ZERO,bOffset] #[0,1], variants := .Single 0,
    backendRepr := .ScalarPair (a := a) (b := b) (bOffset := bOffset),
    largestNiche, uninhabited := false, align := .new align, size,
    maxReprAlign := none, unadjustedAbiAlign := align, reprC := false,
    randomizationSeed := aSize.bytes + bSize.bytes }

/-- Pointer constructor after the caller establishes the pointee's metadata
layout. `none` denotes a sized pointee, not absent or failed metadata evidence. -/
def pointer (target : RuntimeTargetDataLayout) (isReference : Bool)
    (metadata : Option LayoutData) : Except String LayoutData := do
  let value := Primitive.Pointer AddressSpace.ZERO
  let size ← value.size target |>.mapError toString
  let range ← WrappingRange.full size |>.mapError reprStr
  let range := if isReference then {range with start := 1} else range
  let data := Scalar.Initialized (value := value) (validRange := range)
  let thin := scalar target value range
  let some metadata := metadata | return ← thin
  if metadata.is1zst then return ← thin
  let .Scalar metadataScalar := metadata.backendRepr
    | throw "pointer metadata layout is not a scalar or one-byte-aligned ZST"
  scalarPair target data metadataScalar

/-- Pinned rustc_abi/layout.rs::layout_of_array_like for sized arrays. The
exclusive object-size bound is checked before any resulting layout is returned. -/
def arrayLike (target : RuntimeTargetDataLayout) (element : LayoutData)
    (count : UInt64) : Except String LayoutData := do
  let some size := element.size.checkedMul count target.base
    | throw "array layout exceeds target object-size bound"
  return {
    variants := .Single 0, fields := .Array element.size count,
    backendRepr := .Memory (sized := true),
    largestNiche := if count != 0 then element.largestNiche else none,
    uninhabited := element.uninhabited && count != 0,
    align := element.align, size, maxReprAlign := none,
    unadjustedAbiAlign := element.align.abi, reprC := element.reprC,
    randomizationSeed := element.randomizationSeed + count }

end Miri.ABI.PrimitiveLayout
