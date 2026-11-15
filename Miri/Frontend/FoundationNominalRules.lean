import Miri.Frontend.Foundation
import Miri.Input.Model.Types

/-! A deliberately narrow declaration-driven nominal layout component. No nominal
TypeNode/trait fact is claimed. The rules are pinned rustc_abi/layout.rs
layout_of_univariant_biased (one scalar-pair field and trailing alignment-one
ZSTs), and layout_of_enum (two one-field variants, null niche at offset zero).
All seeds come from declaration repr material and recursively computed fields.
The tagged candidate is strictly larger for this subset: its nonzero tag prefix
precedes a two-word, word-aligned payload. No layout answer catalog is consumed. -/
namespace Miri.Frontend.Foundation
open Lean
private def field := Json.getObjVal?
private def nat (j : Json) (key : String) := j.getObjValAs? Nat key
private def string (j : Json) (key : String) := j.getObjValAs? String key
private def array (j : Json) (key : String) := j.getObjValAs? (Array Json) key

private def addSeed (a b : Nat) : Nat := (UInt64.ofNat a + UInt64.ofNat b).toNat
private def fieldsAt (offsets : Array Nat) : Input.FieldShape :=
  ⟨.arbitrary, offsets.size, none, none, offsets, (List.range offsets.size).toArray⟩
private def mem : Input.BackendRepr :=
  ⟨.memory, some true, none, none, none, none, none, none, none⟩

private def reprSeed (repr : Json) (allowed : Array Nat) : Except String Nat := do
  unless allowed.contains (← nat repr "flags_bits") do throw "unsupported nominal repr flags"
  for key in #["align_bytes", "integer", "pack_bytes", "scalable_element"] do
    unless (← field repr key) == Json.null do throw "unsupported nominal repr modifier"
  nat repr "field_shuffle_seed"

private def nonnullPair (l : Input.Layout) : Except String Input.Layout := do
  let some b := l.backendRepresentation | throw "pointer backend absent"
  let some a := b.first | throw "nonnull subset requires scalar pair"
  let some z := b.second | throw "pointer metadata absent"
  let w := a.primitive.sizeBytes
  unless b.kind == .scalarPair && a.primitive.kind == .pointer &&
      a.primitive.addressSpace == some 0 && a.validRange == some (0, 2^(w*8)-1) &&
      z.primitive.kind == .pointer && z.validRange == some (1, 2^(w*8)-1) &&
      l.sizeBytes == some (2*w) && b.secondOffsetBytes == some w do
    throw "unsupported nonnull source pattern layout"
  let a := { a with validRange := some (1, 2^(w*8)-1) }
  return { l with
    fields := some (fieldsAt #[0]), fieldOffsetsBytes := (.explicit #[0]),
    backendRepresentation := some { b with first := some a },
    largestNiche := some ⟨0, a.primitive, (1, 2^(w*8)-1)⟩ }

private def wrapperLayout (empty : Input.Layout) (seed : Nat)
    (fs : Array Input.Layout) : Except String Input.Layout := do
  let combined := fs.foldl (fun s f => addSeed s f.randomizationSeed) seed
  if fs.isEmpty then return { empty with randomizationSeed := combined }
  let some first := fs[0]? | throw "missing wrapper field"
  let some backend := first.backendRepresentation | throw "missing wrapper backend"
  let some size := first.sizeBytes | throw "missing wrapper size"
  unless (backend.kind == .scalar || backend.kind == .scalarPair) && size > 0 do throw "unsupported nominal non-ZST field"
  for f in fs.extract 1 fs.size do
    unless f.sizeBytes == some 0 && f.abiAlignBytes == some 1 && !f.uninhabited do
      throw "unsupported nominal trailing field"
  let offsets := #[0] ++ Array.replicate (fs.size-1) size
  return { first with
    fields := some (fieldsAt offsets), fieldOffsetsBytes := (.explicit offsets),
    randomizationSeed := combined }

private def nicheResult (seed : Nat) (ok err : Input.Layout) : Except String Input.Layout := do
  let some b := err.backendRepresentation | throw "missing error backend"
  let some a := b.first | throw "missing error data scalar"
  let some z := b.second | throw "missing error metadata scalar"
  let w := a.primitive.sizeBytes
  let some ob := ok.backendRepresentation | throw "missing success backend"
  let some os := ob.scalar | throw "unsupported success payload"
  unless w > 0 && w ≤ 16 && err.sizeBytes == some (2*w) && err.abiAlignBytes == some w &&
      err.unadjustedAbiAlignBytes == some w && b.kind == .scalarPair &&
      b.secondOffsetBytes == some w && a.primitive.kind == .pointer &&
      a.primitive.addressSpace == some 0 && z.primitive.kind == .pointer &&
      z.primitive.addressSpace == some 0 && z.primitive.sizeBytes == w &&
      a.validRange == some (1, 2^(w*8)-1) && z.validRange == some (1, 2^(w*8)-1) &&
      ok.sizeBytes == some w && ok.abiAlignBytes == some w &&
      ob.kind == .scalar && os.primitive.kind == .integer && os.primitive.signed == some true &&
      os.validRange == some (0, 2^(w*8)-1) && !ok.uninhabited && !err.uninhabited do
    throw "unsupported two-variant niche layout"
  let tag := { a with validRange := some (0, 2^(w*8)-1) }
  let variants : Array Input.LayoutVariant := #[
    ⟨fieldsAt #[w], none, 0, 2*w, mem, #[w], false⟩,
    ⟨fieldsAt #[0], err.largestNiche, 1, 2*w, b, #[0], false⟩]
  let combined := addSeed seed (addSeed (addSeed seed ok.randomizationSeed)
    (addSeed seed err.randomizationSeed))
  return { err with
    fields := some (fieldsAt #[0]), fieldOffsetsBytes := (.explicit #[0]),
    variantsLayout := some ⟨.multiple, none, some tag,
      some ⟨.niche, some 1, some (0,0), some 0⟩, some 0, variants⟩,
    variantsKind := some .multiple, backendRepresentation := some mem,
    backendReprKind := some .memory, largestNiche := none, randomizationSeed := combined }

/-- Field types instantiated from the original generic declaration. -/
def nominalFields (d : Document) (definition : Nat) (arguments : Array ConcreteType) :
    Except String (Array (Array ConcreteType)) := do
  let some defn := d.definitions[definition]? | throw "nominal declaration absent"
  let adt ← field defn "adt"
  let mut result := #[]
  for v in ← array adt "variants" do
    let mut fields := #[]
    for f in ← array v "fields" do
      fields := fields.push (← instantiate (arguments.map some) #[] (← typeExpr d (← nat f "type")))
    result := result.push fields
  return result

/-- The callback computes only nonnominal leaves. All nominal recursion and
source substitutions are performed here, without compiler answers. -/
def nominalPhysicalLayout (d : Document) (leaf : ConcreteType → Except String Input.Layout)
    (ty : ConcreteType) : Except String Input.Layout := go 256 ty
where
  go (fuel : Nat) (ty : ConcreteType) : Except String Input.Layout := do
    let .succ fuel := fuel | throw "nominal layout recursion exhausted"
    match ty with
    | .patternNotNull base => nonnullPair (← go fuel base)
    | .nominal definition args =>
      let some defn := d.definitions[definition]? | throw "nominal declaration absent"
      let adt ← field defn "adt"
      let sourceVariants ← array adt "variants"
      let fields ← nominalFields d definition args
      let repr ← field adt "representation"
      if (← string adt "kind") == "struct" then
        unless fields.size == 1 do throw "unsupported struct variants"
        let some fs := fields[0]? | throw "struct fields absent"
        let seed ← reprSeed repr #[0,4,8]
        wrapperLayout (← leaf (.tuple #[])) seed (← fs.mapM (go fuel))
      else
        unless (← string adt "kind") == "enum" && fields.size == 2 do
          throw "unsupported nominal kind"
        let seed ← reprSeed repr #[0]
        let mut layouts := #[]
        for i in [0:2] do
          let some v := sourceVariants[i]? | throw "enum variant absent"
          let disc ← field v "discriminant"
          unless (← nat v "index") == i && (← string disc "kind") == "relative" &&
              (← nat disc "distance") == i do throw "unsupported enum discriminant source"
          let some fs := fields[i]? | throw "variant fields absent"
          unless fs.size == 1 do throw "unsupported enum variant fields"
          let some f := fs[0]? | throw "variant field absent"
          layouts := layouts.push (← go fuel f)
        let some ok := layouts[0]? | throw "success layout absent"
        let some err := layouts[1]? | throw "error layout absent"
        nicheResult seed ok err
    | _ => leaf ty
end Miri.Frontend.Foundation
