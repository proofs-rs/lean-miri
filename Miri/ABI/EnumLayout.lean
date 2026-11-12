import Miri.ABI.EnumDiscriminantLayout
import Miri.ABI.NicheEnumLayout
import Miri.ABI.StructLayout

/-! Pinned rustc_abi layout_of_struct_or_enum/layout_of_enum: source child layouts
and evaluated discriminant values produce exact tagged/niche candidates. -/
namespace Miri.ABI.EnumLayout
private def maxAlignment (a b : Option Align) : Option Align :=
  match a,b with
  | some a,some b => some (a.max b)
  | some a,none => some a | none,some b => some b | none,none => none
private def layoutAt (layouts : Array VariantLayout) (i : Nat) : Except String VariantLayout :=
  match layouts[i]? with | some value => .ok value | none => .error "tagged enum variant index absent"
private def fromScalar (target : RuntimeTargetDataLayout) (value : Scalar) : Except String (Option Niche) := do
  let .Initialized (value := value) (validRange := range) := value | return none
  let niche : Niche := ⟨Size.ZERO,value,range⟩
  return if (← NicheLayout.available target niche).toNat > 0 then some niche else none
private def matchingPrimitive (target : RuntimeTargetDataLayout) (a b : Primitive) :
    Except String (Option Primitive) := do
  if a == b then return some a
  match a,b with
  | .Int left sign,.Int right _ => return if left == right then some (.Int left sign) else none
  | .Pointer _,.Int .. | .Int ..,.Pointer _ =>
    if (← a.size target |>.mapError toString) == (← b.size target |>.mapError toString) &&
        (← a.defaultAlign target |>.mapError toString) == (← b.defaultAlign target |>.mapError toString) then
      return some (match a with | .Pointer _ => a | _ => b)
    return none
  | _,_ => return none

/-- Pinned layout_of_enum tagged calculation. Discriminants are evaluated source
values supplied by the caller, not enum layout answers. -/
def tagged (target : RuntimeTargetDataLayout) (variants : Array (Array LayoutData))
    (repr : UnivariantLayout.Representation) (integerRepr : Option IntegerType)
    (discriminants : Array U128) : Except String LayoutData := do
  unless repr.pack.isNone do throw "packed enum representation is invalid"
  unless variants.size == discriminants.size do throw "enum discriminant count mismatch"
  let discrType := integerRepr.getD (.Pointer true)
  let discrInteger ← Integer.fromAttr target discrType |>.mapError reprStr
  let necessary := (variants.toList.zip discriminants.toList).filterMap fun (fields,value) =>
    if repr.flags &&& 1 != 0 || fields.all (! ·.uninhabited) then some value else none
  let mut minimum : Int := 0
  let mut maximum : U128 := 0
  for value in necessary do
    if discrType.isSigned then
      let signed ← discrInteger.size.signExtend value |>.mapError reprStr
      if signed < 0 then minimum := min minimum signed
      else maximum := if signed.toNat > maximum.toNat then BitVec.ofNat 128 signed.toNat else maximum
    else maximum := if value.toNat > maximum.toNat then value else maximum
  let (minInteger,signed) ← EnumDiscriminantLayout.select target integerRepr (repr.flags &&& 1 != 0) minimum maximum
  let mut align := target.aggregateAlign
  let mut maxReprAlign := repr.align
  let mut unadjusted := align
  let mut seed := repr.fieldShuffleSeed
  let mut size := Size.ZERO
  let mut startAlign ← Align.fromBytes 256 |>.mapError reprStr
  let mut prefixAlign := (← minInteger.align target |>.mapError reprStr).abi
  if repr.flags &&& 1 != 0 then
    for fields in variants do
      for field in fields do prefixAlign := prefixAlign.max field.align.abi
  let mut layouts : Array VariantLayout := #[]
  for fields in variants do
    let layout ← UnivariantLayout.compute target fields repr (.prefixed minInteger.size prefixAlign)
    for index in ← layout.fields.indexByIncreasingOffset |>.mapError reprStr do
      let some field := fields[index]? | throw "tagged enum child field index absent"
      if !field.is1zst then
        startAlign := startAlign.min field.align.abi
        break
    size := if size.bytes < layout.size.bytes then layout.size else size
    align := align.max layout.align.abi
    maxReprAlign := maxAlignment maxReprAlign layout.maxReprAlign
    unadjusted := unadjusted.max layout.unadjustedAbiAlign
    seed := seed + layout.randomizationSeed
    layouts := layouts.push (← VariantLayout.fromLayout layout |>.mapError reprStr)
  size ← size.alignTo align |>.mapError toString
  unless size.bytes < target.base.objSizeBound do throw "tagged enum exceeds target object-size bound"
  unless discrInteger.size.bytes ≥ minInteger.size.bytes do throw "layout discriminant exceeds type-check discriminant"
  let mut integer ← if repr.flags &&& 1 != 0 || integerRepr.isSome then pure minInteger
    else pure ((← Integer.forAlign target startAlign |>.mapError toString).getD minInteger)
  if integer.size.bytes ≤ minInteger.size.bytes then integer := minInteger
  else
    let oldSize := minInteger.size
    let newSize := integer.size
    layouts ← layouts.mapM fun layout => do
      let offsets ← layout.fieldOffsets.mapM fun offset => do
        if offset.bytes ≤ oldSize.bytes then
          unless offset == oldSize do throw "tag growth overlaps an enum payload field"
          pure newSize
        else pure offset
      return { layout with
        fieldOffsets := offsets
        size := if layout.size.bytes ≤ oldSize.bytes then newSize else layout.size }
  let truncated ← necessary.mapM (fun value => integer.size.truncate value |>.mapError reprStr)
  let range := (← WrappingRange.smallestRangeContaining truncated integer.size |>.mapError reprStr).getD ⟨0,0⟩
  let tag : Scalar := .Initialized (value := .Int integer signed) (validRange := range)
  let mut abi : BackendRepr := .Memory (sized := true)
  if integer.size == size then abi := .Scalar tag
  else
    let mut common : Option (Primitive × Size) := none
    let mut initialized := true
    for i in [:variants.size] do
      let some fields := variants[i]? | throw "tagged enum variant fields absent"
      let layout ← layoutAt layouts i
      let nonZst := (List.range fields.size).filter fun i => (fields[i]?).any (! ·.isZst)
      if nonZst.isEmpty then
        initialized := false
        continue
      unless nonZst.length == 1 do
        common := none
        break
      let some index := nonZst.head? | throw "nonzero tagged field absent"
      let some field := fields[index]? | throw "nonzero tagged field index absent"
      let some offset := layout.fieldOffsets[index]? | throw "tagged field offset absent"
      let .Scalar scalar := field.backendRepr | do
        common := none
        break
      initialized := initialized && (match scalar with | .Initialized => true | _ => false)
      let primitive := scalar.primitive
      if let some (old,oldOffset) := common then
        if oldOffset != offset then
          common := none
          break
        let some value ← matchingPrimitive target old primitive | do
          common := none
          break
        common := some (value,offset)
      else common := some (primitive,offset)
    if let some (primitive,offset) := common then
      let scalar ← if initialized then do
        let primSize ← primitive.size target |>.mapError toString
        let range ← WrappingRange.full primSize |>.mapError reprStr
        pure (Scalar.Initialized (value := primitive) (validRange := range))
        else pure (.Union (value := primitive))
      let pair ← PrimitiveLayout.scalarPair target tag scalar
      let .Arbitrary offsets _ := pair.fields | throw "scalar pair fields not arbitrary"
      if offsets[0]? == some Size.ZERO && offsets[1]? == some offset && align == pair.align.abi && size == pair.size then
        abi := pair.backendRepr
  match abi with
  | .Scalar _ | .ScalarPair =>
    layouts := layouts.map fun layout => match layout.backendRepr with
      | .Memory => if layout.hasFields then { layout with
          backendRepr := abi
          size := if layout.size.bytes < size.bytes then size else layout.size } else layout
      | _ => layout
  | _ => pure ()
  return {
    variants := .Multiple tag .Direct 0 layouts
    fields := .Arbitrary #[Size.ZERO] #[0], largestNiche := ← fromScalar target tag
    uninhabited := layouts.all (·.uninhabited), backendRepr := abi
    align := .new align, size, maxReprAlign, unadjustedAbiAlign := unadjusted
    reprC := repr.flags &&& 1 != 0, randomizationSeed := seed }
end Miri.ABI.EnumLayout

namespace Miri.ABI.EnumLayout
/-- Compare the actual tagged/niche candidates with rustc's size/niche-count
order and tagged tie preference. -/
def compute (target : RuntimeTargetDataLayout) (variants : Array (Array LayoutData))
    (repr : UnivariantLayout.Representation) (integerRepr : Option IntegerType)
    (discriminants : Array U128)
    (niches : StructLayout.NicheOptimizations := .enabled) : Except String LayoutData := do
  unless repr.integerRepresentation == integerRepr.isSome do throw "enum integer repr disagreement"
  let optimized := repr.flags &&& 1 == 0 && !repr.integerRepresentation
  let present := variants.toList.zipIdx.filterMap fun (fields,index) =>
    if !optimized || !(fields.any (·.uninhabited) && fields.all (·.is1zst)) then some index else none
  if present.isEmpty then return ← PrimitiveLayout.compute target "never"
  if optimized && present.length == 1 then
    let some index := present.head? | throw "present enum variant absent"
    let some fields := variants[index]? | throw "present enum variant fields absent"
    return ← StructLayout.compute target fields repr index true true niches
  let tagged ← tagged target variants repr integerRepr discriminants
  let some niche ← NicheEnumLayout.candidate target variants repr | return tagged
  let count (layout : LayoutData) : Except String Nat := do
    let some niche := layout.largestNiche | return 0
    return (← NicheLayout.available target niche).toNat
  return if tagged.size.bytes > niche.size.bytes ||
      (tagged.size == niche.size && (← count tagged) < (← count niche)) then niche else tagged
end Miri.ABI.EnumLayout
