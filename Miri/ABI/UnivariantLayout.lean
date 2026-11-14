import Miri.ABI.PrimitiveLayout
import Miri.ABI.LayoutShuffle

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd,
`rustc_abi/src/layout.rs::{layout_of_univariant,layout_of_univariant_biased}`.
This module ports deterministic field ordering, offset calculation, niche
placement, ABI promotion and pinned rand/Xoshiro randomized ordering. -/
namespace Miri.ABI.UnivariantLayout

structure Representation where
  flags : UInt8 := 0
  integerRepresentation : Bool := false
  align : Option Align := none
  pack : Option Align := none
  fieldShuffleSeed : UInt64 := 0
  deriving Repr

inductive Kind where
  | alwaysSized
  | maybeUnsized
  | prefixed (size : Size) (align : Align)
  deriving Repr, DecidableEq

inductive Bias where
  | start | «end»
  deriving Repr, DecidableEq

private def flag (repr : Representation) (mask : UInt8) : Bool := repr.flags &&& mask != 0
private def inhibitOrder (repr : Representation) : Bool := flag repr 75 || repr.integerRepresentation
private def transparent (repr : Representation) : Bool := flag repr 4
private def c (repr : Representation) : Bool := flag repr 1

private def available (target : RuntimeTargetDataLayout) (niche : Niche) : Except String Nat := do
  let size ← niche.value.size target |>.mapError toString
  let maximum ← size.unsignedIntMax |>.mapError toString
  pure (((niche.validRange.start - (niche.validRange.end + 1)) &&& maximum).toNat)

private def nicheSize (target : RuntimeTargetDataLayout) (field : LayoutData) : Except String Nat :=
  match field.largestNiche with | none => pure 0 | some niche => available target niche

private def maxOption (left right : Option Align) : Option Align :=
  match left,right with
  | some a,some b => some (a.max b)
  | some a,none | none,some a => some a
  | none,none => none

private structure SortKey where
  group : Nat
  niche : Nat
  inner : Nat

private def before (isPrefix : Bool) (left right : SortKey) : Bool :=
  if left.group != right.group then
    if isPrefix then left.group < right.group else left.group > right.group
  else if left.niche != right.niche then left.niche < right.niche
  else left.inner <= right.inner

private def ordering (target : RuntimeTargetDataLayout) (fields : Array LayoutData)
    (repr : Representation) (kind : Kind) (bias : Bias) : Except String (Array Nat × UInt64) := do
  if kind == .maybeUnsized && fields.isEmpty then
    throw "MaybeUnsized layout has no tail field"
  let last := if kind == .maybeUnsized then fields.size - 1 else fields.size
  let head := fields.extract 0 last
  let fieldSeed := head.foldl (fun seed f => seed + f.randomizationSeed) (0 : UInt64)
  let source := (List.range fields.size).toArray
  if inhibitOrder repr || fields.size <= 1 then return (source,fieldSeed)
  if flag repr 16 then
    let (shuffled,_) ← LayoutShuffle.shuffle (source.extract 0 last)
      (LayoutShuffle.seed (fieldSeed + repr.fieldShuffleSeed))
    return (shuffled ++ source.extract last fields.size,fieldSeed)
  let mut maxAlign := 1
  let mut largestNiche := 0
  for field in head do
    let bytes ← field.align.abi.bytes |>.mapError toString
    maxAlign := max maxAlign bytes.toNat
    largestNiche := max largestNiche (← nicheSize target field)
  let mut keys : Array SortKey := #[]
  for field in head do
    let niche ← nicheSize target field
    let group ← match repr.pack with
      | some pack => pure (← (field.align.abi.min pack).bytes |>.mapError toString).toNat
      | none => do
        let align ← field.align.abi.bytes |>.mapError toString
        let sizeAsAlign := (Align.maxAlignedFactor (Size.ofBytes (max align field.size.bytes))).pow2
        let sizeAsAlign := if largestNiche > 0 then
          match bias with
          | .start => min (Align.maxAlignedFactor (Size.ofBytes (UInt64.ofNat maxAlign))).pow2 sizeAsAlign
          | .end => if niche == largestNiche then field.align.abi.pow2 else sizeAsAlign
          else sizeAsAlign
        pure sizeAsAlign
    let nicheKey := if bias == .start then (2^128 - 1) - niche else niche
    let inner ← match field.largestNiche with
      | none => pure 0
      | some niche =>
        if bias == .start then pure niche.offset.bytes.toNat else do
          let size ← niche.value.size target |>.mapError toString
          let distance := field.size.bytes - size.bytes - niche.offset.bytes
          pure ((2^64 - 1) - distance.toNat)
    let isPrefix := match kind with | .prefixed .. => true | _ => false
    keys := keys.push ⟨group,if isPrefix then niche else nicheKey,if isPrefix then 0 else inner⟩
  let prefixOrder := match kind with | .prefixed .. => true | _ => false
  let sorted := (List.range last).mergeSort fun i j =>
    match keys[i]?,keys[j]? with
    | some a,some b => before prefixOrder a b
    | _,_ => false
  return (sorted.toArray ++ source.extract last fields.size,fieldSeed)

/-- One bias pass. Input field layouts are material dependencies; source repr
flags, packing/alignment and the exact struct kind determine all outputs. -/
def biased (target : RuntimeTargetDataLayout) (fields : Array LayoutData)
    (repr : Representation) (kind : Kind) (bias : Bias) : Except String LayoutData := do
  let (order,fieldSeed) ← ordering target fields repr kind bias
  let mut align := if repr.pack.isSome then target.i8Align else target.aggregateAlign
  let mut maxReprAlign := repr.align
  let mut offset := Size.ZERO
  if let .prefixed prefixSize prefixAlign := kind then
    let prefixAlign := repr.pack.map (prefixAlign.min ·) |>.getD prefixAlign
    align := align.max prefixAlign
    offset ← prefixSize.alignTo prefixAlign |>.mapError toString
  let mut offsets := Array.replicate fields.size Size.ZERO
  let mut unsized := false
  let mut largestNiche : Option Niche := none
  let mut largestAvailable := 0
  for index in order do
    let some field := fields[index]? | throw "univariant field order references absent field"
    if unsized then throw "field follows unsized univariant field"
    if field.isUnsized then
      if kind == .maybeUnsized then unsized := true
      else throw "unsized field in sized univariant layout"
    let fieldAlign := match repr.pack with
      | some pack => field.align.min (.new pack) | none => field.align
    offset ← offset.alignTo fieldAlign.abi |>.mapError toString
    align := align.max fieldAlign.abi
    maxReprAlign := maxOption maxReprAlign field.maxReprAlign
    if h : index < offsets.size then offsets := offsets.set index offset h
    else throw "univariant field offset index out of bounds"
    if let some niche := field.largestNiche then
      let count ← available target niche
      if (if bias == .start then count > largestAvailable else count >= largestAvailable) then
        largestAvailable := count
        largestNiche := some {niche with offset := ← niche.offset.add offset |>.mapError toString}
    let some next := offset.checkedAdd field.size target.base
      | throw "univariant field offsets exceed target object-size bound"
    offset := next
  let unadjustedAlign := align
  align := repr.align.map (align.max ·) |>.getD align
  let size ← offset.alignTo align |>.mapError toString
  if size.bytes >= target.base.objSizeBound then
    throw "univariant layout exceeds target object-size bound"
  let sized := !unsized
  let mut abi := BackendRepr.Memory (sized := sized)
  let nonZero := ((List.range fields.size).filter fun i =>
    match fields[i]? with | some field => field.size.bytes != 0 || !field.isSized | none => false).toArray
  let mut singleField : Option LayoutData := none
  if sized && size.bytes > 0 then
    if nonZero.size == 1 then
      let some i := nonZero[0]? | throw "univariant non-ZST index absent"
      let some field := fields[i]? | throw "univariant non-ZST field absent"
      singleField := some field
      if offsets[i]? == some Size.ZERO && align == field.align.abi && size == field.size then
        match field.backendRepr with
        | .Scalar _ | .SimdVector => if !flag repr 3 then abi := field.backendRepr
        | .ScalarPair => abi := field.backendRepr
        | _ => pure ()
    else if nonZero.size == 2 then
      let some i := nonZero[0]? | throw "univariant first non-ZST index absent"
      let some j := nonZero[1]? | throw "univariant second non-ZST index absent"
      let some a := fields[i]? | throw "univariant first non-ZST field absent"
      let some b := fields[j]? | throw "univariant second non-ZST field absent"
      if let .Scalar av := a.backendRepr then
        if let .Scalar bv := b.backendRepr then
          let some ai := offsets[i]? | throw "univariant first field offset absent"
          let some bi := offsets[j]? | throw "univariant second field offset absent"
          let (a,b,ao,bo) := if ai.bytes < bi.bytes then (av,bv,ai,bi) else (bv,av,bi,ai)
          let pair ← PrimitiveLayout.scalarPair target a b
          let .Arbitrary po _ := pair.fields | throw "scalar pair fields are not arbitrary"
          if po[0]? == some ao && po[1]? == some bo && align == pair.align.abi && size == pair.size then
            abi := pair.backendRepr
  let unadjustedAbiAlign := if transparent repr then
    singleField.map (·.unadjustedAbiAlign) |>.getD align else unadjustedAlign
  return {
    variants := .Single 0, fields := .Arbitrary offsets order, backendRepr := abi,
    largestNiche, uninhabited := fields.any (·.uninhabited), align := .new align,
    size, maxReprAlign, unadjustedAbiAlign,
    reprC := c repr || (transparent repr && fields.any (·.reprC)),
    randomizationSeed := fieldSeed + repr.fieldShuffleSeed }

/-- Rustc's second pass chooses the end-biased niche only when it is strictly
closer to an edge under the source's head-space comparison. -/
def compute (target : RuntimeTargetDataLayout) (fields : Array LayoutData)
    (repr : Representation := {}) (kind : Kind := .alwaysSized) : Except String LayoutData := do
  let layout ← biased target fields repr kind .start
  if kind == .maybeUnsized then return layout
  let some niche := layout.largestNiche | return layout
  let nicheSize ← niche.value.size target |>.mapError toString
  let head := niche.offset.bytes
  let tail := layout.size.bytes - head - nicheSize.bytes
  if fields.size <= 1 || head == 0 || tail == 0 then return layout
  let alternate ← biased target fields repr kind .end
  let some altNiche := alternate.largestNiche
    | throw "end-biased univariant layout lost its niche"
  if alternate.size != layout.size then throw "univariant bias changed layout size"
  let altHead := altNiche.offset.bytes
  return if altHead > head && altHead > tail then alternate else layout

end Miri.ABI.UnivariantLayout
