import Miri.ABI.UnivariantLayout

/-! Pinned rustc_abi/src/layout/coroutine.rs. Inputs are saved-local child
layouts, upvar child layouts and raw transformed-MIR field/conflict relations.
The caller separately instantiates MaybeUninit<T> local types and applies the
physical definition hash seed as rustc_ty_utils::layout does. -/
namespace Miri.ABI.CoroutineLayout
private inductive Assignment where
  | unassigned
  | assigned (variant : Nat)
  | ineligible (prefixField : Option Nat)
  deriving BEq
private def checkedAt (values : Array α) (index : Nat) (what : String) : Except String α :=
  match values[index]? with | some value => pure value | none => .error s!"coroutine {what} index absent"
private def replace (values : Array α) (index : Nat) (value : α) (what : String) : Except String (Array α) :=
  if bounded : index < values.size then pure (values.set index value bounded)
  else .error s!"coroutine {what} update index absent"
private def assignments (locals : Nat) (variants conflicts : Array (Array Nat)) :
    Except String (Array Nat × Array Assignment) := do
  unless conflicts.size == locals do throw "coroutine conflict matrix dimension mismatch"
  for row in conflicts do
    unless row.all (· < locals) && row.toList.eraseDups.length == row.size do
      throw "coroutine conflict matrix index out of range or duplicate"
  for row in variants do
    unless row.all (· < locals) do throw "coroutine variant savedLocal index out of range"
  let mut assigned := Array.replicate locals Assignment.unassigned
  let mut ineligible : Array Bool := Array.replicate locals false
  for (fields,i) in variants.toList.zipIdx do
    for savedLocal in fields do
      match ← checkedAt assigned savedLocal "saved-local assignment" with
      | .unassigned => assigned ← replace assigned savedLocal (.assigned i) "saved-local assignment"
      | .assigned _ =>
        ineligible ← replace ineligible savedLocal true "saved-local eligibility"
        assigned ← replace assigned savedLocal (.ineligible none) "saved-local assignment"
      | .ineligible _ => pure ()
  for (row,a) in conflicts.toList.zipIdx do
    let countA := row.size
    if ← checkedAt ineligible a "conflict eligibility" then continue
    -- BitMatrix iterates set bits in ascending index order.
    for b in row.qsort (· < ·) do
      if (← checkedAt ineligible b "conflict eligibility") ||
          (← checkedAt assigned a "conflict assignment") == (← checkedAt assigned b "conflict assignment") then continue
      let countB := (← checkedAt conflicts b "conflict row").size
      let remove := if countA > countB then a else b
      ineligible ← replace ineligible remove true "conflict eligibility"
      assigned ← replace assigned remove (.ineligible none) "conflict assignment"
  let used := assigned.toList.filterMap fun assignment => match assignment with
    | .assigned i => some i | _ => none
  if used.eraseDups.length < 2 then
    assigned := Array.replicate locals (.ineligible none)
    ineligible := Array.replicate locals true
  let promoted := (ineligible.toList.zipIdx.filterMap fun (isPromoted,index) => if isPromoted then some index else none).toArray
  for (savedLocal,index) in promoted.toList.zipIdx do
    assigned ← replace assigned savedLocal (.ineligible (some index)) "promoted assignment"
  pure (promoted,assigned)

private def inverse (order : Array Nat) : Except String (Array Nat) := do
  let mut result := Array.replicate order.size 0
  let mut seen : Array Nat := #[]
  for memory in [:order.size] do
    let field ← checkedAt order memory "memory order"
    unless field < order.size && !seen.contains field do throw "coroutine memory order is not a permutation"
    seen := seen.push field
    result ← replace result field memory "inverse memory order"
  pure result

def compute (target : RuntimeTargetDataLayout) (locals prefixLayout : Array LayoutData)
    (variantFields conflicts : Array (Array Nat)) : Except String LayoutData := do
  unless !variantFields.isEmpty do throw "coroutine has no reserved variants"
  let (promoted,assigned) ← assignments locals.size variantFields conflicts
  let tagIndex := prefixLayout.size
  let maxDiscr : U128 := BitVec.ofNat 128 (variantFields.size-1)
  let integer := Integer.fitUnsigned maxDiscr
  let tag : Scalar := .Initialized (value := .Int integer false) (validRange := ⟨0,maxDiscr⟩)
  let tagLayout ← PrimitiveLayout.scalar target (.Int integer false) ⟨0,maxDiscr⟩
  let promotedLayouts ← promoted.mapM (fun savedLocal => checkedAt locals savedLocal "promoted savedLocal")
  let prefixLayout ← UnivariantLayout.compute target (prefixLayout.push tagLayout ++ promotedLayouts)
  let .Arbitrary prefixOffsets prefixOrder := prefixLayout.fields | throw "coroutine prefixLayout fields not arbitrary"
  let split := tagIndex+1
  let outerOffsets := prefixOffsets.extract 0 split
  let promotedOffsets := prefixOffsets.extract split prefixOffsets.size
  let outerOrder := prefixOrder.filter (· < split)
  let promotedOrder := (prefixOrder.filter (· ≥ split)).map (·-split)
  let promotedMemory ← inverse promotedOrder
  let mut size := prefixLayout.size
  let mut align := prefixLayout.align
  let mut variants : Array VariantLayout := #[]
  for (fields,index) in variantFields.toList.zipIdx do
    let mut exclusive : Array LayoutData := #[]
    for savedLocal in fields do
      match ← checkedAt assigned savedLocal "variant assignment" with
      | .assigned i =>
        unless i == index do throw "coroutine saved-savedLocal assignment disagrees with variant"
        exclusive := exclusive.push (← checkedAt locals savedLocal "exclusive savedLocal")
      | .ineligible _ => pure ()
      | .unassigned => throw "coroutine variant references an unassigned savedLocal"
    let variant ← UnivariantLayout.compute target exclusive {} (.prefixed prefixLayout.size prefixLayout.align.abi)
    let .Arbitrary offsets order := variant.fields | throw "coroutine variant fields not arbitrary"
    let memory ← inverse order
    let invalid := promotedMemory.size + memory.size
    let mut combinedOrder := Array.replicate invalid invalid
    let mut combinedOffsets : Array Size := #[]
    let mut exclusiveIndex := 0
    for (savedLocal,i) in fields.toList.zipIdx do
      let (offset,memoryIndex) ← match ← checkedAt assigned savedLocal "variant assignment" with
        | .unassigned => throw "coroutine variant references an unassigned savedLocal"
        | .assigned _ => do
          let offset ← checkedAt offsets exclusiveIndex "exclusive field offset"
          let memory ← checkedAt memory exclusiveIndex "exclusive field memory order"
          exclusiveIndex := exclusiveIndex+1
          pure (offset,promotedMemory.size+memory)
        | .ineligible (some field) => do
          pure (← checkedAt promotedOffsets field "promoted offset",← checkedAt promotedMemory field "promoted memory order")
        | .ineligible none => throw "coroutine promoted field assignment absent"
      unless memoryIndex < combinedOrder.size do throw "coroutine combined memory order out of range"
      combinedOrder ← replace combinedOrder memoryIndex i "combined memory order"
      combinedOffsets := combinedOffsets.push offset
    combinedOrder := combinedOrder.filter (· != invalid)
    let variant := { variant with fields := .Arbitrary combinedOffsets combinedOrder }
    size := if size.bytes < variant.size.bytes then variant.size else size
    align := align.max variant.align
    variants := variants.push (← VariantLayout.fromLayout variant |>.mapError reprStr)
  size ← size.alignTo align.abi |>.mapError toString
  return {
    variants := .Multiple tag .Direct tagIndex variants
    fields := .Arbitrary outerOffsets outerOrder, backendRepr := .Memory (sized := true)
    largestNiche := none, uninhabited := prefixLayout.uninhabited || variants.all (·.uninhabited)
    size, align, maxReprAlign := none, unadjustedAbiAlign := align.abi
    reprC := false, randomizationSeed := 0 }
end Miri.ABI.CoroutineLayout
