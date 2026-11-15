import Miri.Input.RuntimeMetadata

/-! Pinned rustc_abi/layout.rs::layout_of_univariant_biased, default repr,
positive-sized initialized scalar/scalar-pair fields. Three or more non-ZST
fields have Memory ABI. Tuple MaybeUnsized excludes the tail from ordering and
seed; closure AlwaysSized includes it. Cases requiring the unported end-biased
retry, zero-sized/unsized fields or two-field ABI optimization reject. -/
namespace Miri.Input.SourceLayouts

private def aligned (n a : Nat) : Nat := (n+a-1)/a*a
private def trailing (n : Nat) : Nat := (List.range 128).find? (fun i => n % (2^(i+1)) != 0) |>.getD 128
private def available (n : Option Input.NicheLayout) : Nat := match n with
  | none => 0
  | some n =>
    let limit := 2^(n.primitive.sizeBytes*8)
    let (lo,hi) := n.validRange
    limit - (if lo ≤ hi then hi-lo+1 else limit-lo+hi+1)

/-- Size/alignment for the supported positive-sized fields. Ordering a field
within its effective alignment class cannot change size: each field's size is
a multiple of that effective alignment. The tail stays last for tuples. -/
def scalarAggregateSize (aggregate bound : Nat) (fields : Array (Nat × Nat))
    (tupleTail : Bool) : Except String (Nat × Nat) := do
  unless fields.size ≥ 3 do throw "aggregate requires at least three non-ZST fields"
  let end_ := fields.size - (if tupleTail then 1 else 0)
  for (size,align) in fields do
    unless size > 0 && align > 0 && size % align == 0 && 2^(trailing align) == align do
      throw "unsupported aggregate field size/alignment"
  let leading := (fields.extract 0 end_).toList.mergeSort (fun a b => a.2 ≥ b.2)
  let ordered := leading.toArray ++ fields.extract end_ fields.size
  let mut offset := 0
  let mut align := aggregate
  for (size,a) in ordered do
    offset := aligned offset a + size
    align := max align a
  let size := aligned offset align
  unless size < bound do throw "aggregate exceeds target object bound"
  return (size,align)

/-- Exact supported scalar aggregate row. No field offsets, ordering, niche or
seed is read from compiler answers. -/
def scalarAggregateLayout (target : ABI.RuntimeTargetDataLayout)
    (fields : Array Input.Layout) (tupleTail : Bool) : Except String Input.Layout := do
  let aggregate := (← target.aggregateAlign.bytes.mapError toString).toNat
  let mut sizes := #[]
  for field in fields do
    let some size := field.sizeBytes | throw "aggregate field size absent"
    let some align := field.abiAlignBytes | throw "aggregate field alignment absent"
    let some b := field.backendRepresentation | throw "aggregate field backend absent"
    unless (b.kind == .scalar || b.kind == .scalarPair) && !field.uninhabited &&
        field.maxReprAlignBytes.isNone && !field.reprC do
      throw "aggregate field outside scalar/pair subset"
    sizes := sizes.push (size,align)
  let (size,align) ← scalarAggregateSize aggregate target.base.objSizeBound.toNat sizes tupleTail
  let end_ := fields.size - (if tupleTail then 1 else 0)
  let leading := fields.extract 0 end_
  let maxAlign := leading.foldl (fun n f => max n (f.abiAlignBytes.getD 1)) 1
  let maxNiche := leading.foldl (fun n f => max n (available f.largestNiche)) 0
  let key := fun (i : Nat) => do
    let some f := fields[i]? | throw "aggregate field index absent"
    let a := f.abiAlignBytes.getD 1
    let s := f.sizeBytes.getD 0
    let group := trailing (max a s)
    pure (if maxNiche > 0 then min (trailing maxAlign) group else group,
      available f.largestNiche, f.largestNiche.map (·.offsetBytes) |>.getD 0)
  let mut order := #[]
  -- Stable insertion sort: group descending, niche availability descending,
  -- internal niche offset ascending; original source order breaks ties.
  for i in [:end_] do
    let (g,n,o) ← key i
    let mut position := order.size
    for j in [:order.size] do
      let some previous := order[j]? | throw "aggregate order index absent"
      let (pg,pn,po) ← key previous
      if position == order.size && (g > pg || (g == pg && (n > pn || (n == pn && o < po)))) then
        position := j
    order := order.extract 0 position ++ #[i] ++ order.extract position order.size
  order := order ++ (List.range (fields.size-end_)).toArray.map (· + end_)
  let mut offsets := Array.replicate fields.size 0
  let mut offset := 0
  let mut niche := none
  let mut largest := 0
  for i in order do
    let some field := fields[i]? | throw "aggregate source field absent"
    offset := aligned offset (field.abiAlignBytes.getD 1)
    if h : i < offsets.size then
      offsets := offsets.set i offset h
    else throw "aggregate offset index absent"
    if let some n := field.largestNiche then
      if available (some n) > largest then
        largest := available (some n)
        niche := some { n with offsetBytes := n.offsetBytes + offset }
    offset := offset + field.sizeBytes.getD 0
  unless aligned offset align == size do throw "aggregate size/order contradiction"
  if !tupleTail then
    if let some n := niche then
      unless n.offsetBytes == 0 || size - n.offsetBytes - n.primitive.sizeBytes == 0 do
        throw "aggregate requires end-biased niche layout retry"
  let some first := fields[0]? | throw "aggregate first field absent"
  let seed := leading.foldl (fun s f => (UInt64.ofNat s + UInt64.ofNat f.randomizationSeed).toNat) 0
  let backend : Input.BackendRepr := ⟨.memory, some true, none, none, none, none, none, none, none⟩
  return { first with
    sizeBytes := some size, abiAlignBytes := some align, unadjustedAbiAlignBytes := some align,
    fields := some ⟨.arbitrary, fields.size, none, none, offsets, order⟩,
    fieldOffsetsBytes := .explicit offsets, randomizationSeed := seed, largestNiche := niche,
    variantsLayout := some ⟨.single, some 0, none, none, none, #[]⟩,
    variantsKind := some .single, backendRepresentation := some backend, backendReprKind := some .memory }
end Miri.Input.SourceLayouts
