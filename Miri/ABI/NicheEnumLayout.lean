import Miri.ABI.NicheLayout
import Miri.ABI.UnivariantLayout
import Miri.ABI.PrimitiveLayout

namespace Miri.ABI.NicheEnumLayout
private def maxAlignment (a b : Option Align) : Option Align :=
  match a,b with
  | some a,some b => some (a.max b)
  | some a,none => some a | none,some b => some b | none,none => none
private def layoutAt (layouts : Array VariantLayout) (i : Nat) : Except String VariantLayout :=
  match layouts[i]? with
  | some layout => .ok layout
  | none => .error "niche candidate internal variant index absent"

private def fromScalar (target : RuntimeTargetDataLayout) (offset : Size) (scalar : Scalar) :
    Except String (Option Niche) := do
  let .Initialized (value := value) (validRange := range) := scalar | return none
  let niche : Niche := ⟨offset,value,range⟩
  return if (← NicheLayout.available target niche).toNat > 0 then some niche else none

/-- The niche candidate from pinned layout_of_enum, before comparison against
its tagged candidate. Inputs are child LayoutData, not cached enum answers. -/
def candidate (target : RuntimeTargetDataLayout) (variants : Array (Array LayoutData))
    (repr : UnivariantLayout.Representation) : Except String (Option LayoutData) := do
  if repr.flags &&& 1 != 0 || repr.integerRepresentation || variants.size < 2 then return none
  let mut align := target.aggregateAlign
  let mut maxReprAlign := repr.align
  let mut unadjusted := align
  let mut seed := repr.fieldShuffleSeed
  let mut infos : Array Align := #[]
  let mut layouts : Array VariantLayout := #[]
  for fields in variants do
    let .ok layout := UnivariantLayout.compute target fields repr .alwaysSized | return none
    infos := infos.push layout.align.abi
    align := align.max layout.align.abi
    maxReprAlign := maxAlignment maxReprAlign layout.maxReprAlign
    unadjusted := unadjusted.max layout.unadjustedAbiAlign
    seed := seed + layout.randomizationSeed
    layouts := layouts.push (← VariantLayout.fromLayout layout |>.mapError reprStr)
  let mut largest := 0
  for i in [:layouts.size] do
    if (← layoutAt layouts i).size.bytes ≥ (← layoutAt layouts largest).size.bytes then largest := i
  let needsTag := variants.toList.zipIdx.filterMap fun (fields,index) =>
    if index != largest && !(fields.any (·.uninhabited) && fields.all (·.is1zst)) then some index else none
  let some start := needsTag.head? | return none
  let some stop := needsTag.getLast? | return none
  let count : U128 := BitVec.ofNat 128 (stop-start+1)
  let largestLayout ← layoutAt layouts largest
  let some largestAlign := infos[largest]? | throw "niche candidate alignment index absent"
  let some niche := largestLayout.largestNiche | return none
  let some (nicheStart,nicheScalar) ← NicheLayout.reserve target niche count | return none
  let nicheOffset := niche.offset
  let nicheSize ← niche.value.size target |>.mapError toString
  let size ← largestLayout.size.alignTo align |>.mapError toString
  for i in [:layouts.size] do
    if i == largest then continue
    let original ← layoutAt layouts i
    let mut layout := { original with largestNiche := none }
    if layout.size.bytes > nicheOffset.bytes then
      let some variantAlign := infos[i]? | throw "niche candidate alignment index absent"
      let offset ← (← nicheOffset.add nicheSize |>.mapError toString).alignTo variantAlign |>.mapError toString
      if (← offset.add layout.size |>.mapError toString).bytes > size.bytes then return none
      layout := { layout with
        fieldOffsets := ← layout.fieldOffsets.mapM (fun field => field.add offset |>.mapError toString)
        backendRepr := if layout.uninhabited then layout.backendRepr else .Memory (sized := true)
        size := ← layout.size.add offset |>.mapError toString }
    if bounded : i < layouts.size then layouts := layouts.set i layout bounded
    else throw "niche candidate variant update index absent"
  let largestNiche ← fromScalar target nicheOffset nicheScalar
  let othersZst := layouts.toList.zipIdx.all fun (layout,index) => index == largest || layout.size.bytes == 0
  let abi : BackendRepr := if size == largestLayout.size && align == largestAlign && othersZst then
    match largestLayout.backendRepr with
    | .Scalar _ => .Scalar nicheScalar
    | .ScalarPair (a := a) (b := b) (bOffset := offset) =>
      if nicheOffset.bytes == 0 then .ScalarPair (a := nicheScalar) (b := b.toUnion) (bOffset := offset)
      else .ScalarPair (a := a.toUnion) (b := nicheScalar) (bOffset := offset)
    | _ => .Memory (sized := true)
    else .Memory (sized := true)
  return some {
    variants := .Multiple nicheScalar (.Niche largest start stop nicheStart) 0 layouts
    fields := .Arbitrary #[nicheOffset] #[0]
    backendRepr := abi, largestNiche, uninhabited := layouts.all (·.uninhabited)
    size, align := .new align, maxReprAlign, unadjustedAbiAlign := unadjusted
    reprC := repr.flags &&& 1 != 0, randomizationSeed := seed }
end Miri.ABI.NicheEnumLayout
