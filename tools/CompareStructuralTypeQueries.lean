import Miri.Input.TableCore
import Lean.Data.Json.Printer
import Miri.Input.StructuralDeref
import Miri.Input.StructuralTail
import Miri.Input.StructuralAutoTraits
import Miri.Input.StructuralSized

/-! Differential adapter: input must be a fresh canonical baseline export from
the pinned rustc. Old result rows are oracle data only; production queries do
not read these rows. This driver compares every exported type, not just roots. -/
open Miri.Input

-- Decode only the category under comparison. Incompatible ABI and runtime
-- catalogs are never read, rewritten or supplied with guessed material.
private def readTypes (source : String) : Except String (Array TypeNode) := do
  let value ← Lean.Json.parse source
  unless (← (← value.getObjVal? "schema_version").getNat?) == 12 do
    throw "oracle reader requires canonical baseline schema 12"
  let booleans ← value.getObjVal? "boolean_queries"
  let discriminants ← value.getObjVal? "discriminants"
  let pool ← JsonReader.run (JsonReader.array DecoderValues.booleanQueries) booleans.compress
  let discriminants ← JsonReader.run (JsonReader.array DecoderValues.parseDiscriminants) discriminants.compress
  let types ← value.getObjVal? "types"
  JsonReader.run (JsonReader.array (DecoderValues.parseTypeNode "$oracle.types" pool discriminants)) types.compress

private def check (nodes : Array TypeNode) : Except String (Nat × Nat × Nat × Nat × Nat × Nat) := do
  let lookup (id : Nat) : Except String TypeNode := do
    let some node := nodes.find? (·.id == id) | throw s!"absent type {id}"
    return node
  let oracle (id : Nat) (key : String) : Except String (Option Nat) := do
    let some facts := (← lookup id).compilerFacts | throw "oracle facts absent"
    let some (_, result) := facts.typeQueries.find? (·.1 == key)
      | throw s!"oracle query absent: {key}"
    return result
  let normalize (id : Nat) : Except String Nat := do
    let some result ← oracle id "normalized" | throw "normalization oracle absent"
    return result
  let mut comparisons := 0
  let mut boxes := 0
  let mut pointers := 0
  let mut changedTails := 0
  let mut autoTraitTrue := 0
  let mut autoTraitResidual := 0
  let mut sizedPositive := 0
  let mut sizedNegative := 0
  for node in nodes do
    let some facts := node.compilerFacts | throw "oracle facts absent"
    let some (_, isBox) := facts.booleanQueries.find? (·.1 == "is_box")
      | throw "Box identity absent"
    if isBox then boxes := boxes + 1
    if node.shapeKind == .rawPointer then pointers := pointers + 1
    let normalized ← normalize node.id
    let trivial ← StructuralAutoTraits.trivial (fun id => return (← lookup id).shape)
      (nodes.size + 1) normalized
    for key in #["is_freeze", "is_unpin", "is_unsafe_unpin"] do
      let some (_, expected) := facts.booleanQueries.find? (·.1 == key)
        | throw s!"auto-trait oracle absent: {key}"
      if trivial then
        unless expected do throw s!"type {node.id} {key}: Lean trivial=true, rustc=false"
        autoTraitTrue := autoTraitTrue + 1
      else autoTraitResidual := autoTraitResidual + 1
    if let some sized ← StructuralSized.query (fun id => do
        pure (← lookup (← normalize id)).shape) (nodes.size + 1) node.id then
      let some (_, expected) := facts.booleanQueries.find? (·.1 == "is_sized")
        | throw "Sized oracle absent"
      unless sized == expected do throw s!"type {node.id}: Lean Sized={sized}, rustc={expected}"
      if sized then sizedPositive := sizedPositive + 1 else sizedNegative := sizedNegative + 1
    let queryNode ← lookup (node.layoutQueryInputTypeId.getD node.id)
    let results := #[
      ("boxed_type", ← StructuralDeref.boxedType queryNode.shape isBox),
      ("builtin_deref_explicit", ← StructuralDeref.builtinDeref queryNode.shape isBox true),
      ("builtin_deref_implicit", ← StructuralDeref.builtinDeref queryNode.shape isBox false),
      ("metadata_tail", some (← StructuralTail.tail (fun id => return (← lookup id).shape)
        normalize (nodes.size + 1) (← normalize node.id)))]
    for (key, actual) in results do
      let expected ← oracle node.id key
      unless actual == expected do
        throw s!"type {node.id} {key}: Lean={actual}, rustc={expected}"
      if key == "metadata_tail" && actual != some node.id then
        changedTails := changedTails + 1
      comparisons := comparisons + 1
  unless boxes > 0 && pointers > 0 && changedTails > 0 do
    throw "oracle fixture does not cover Box, raw pointers and nontrivial tails"
  unless autoTraitTrue > 0 && autoTraitResidual > 0 do
    throw "oracle fixture does not cover trivial and residual auto-trait branches"
  -- Residual rows are counted, not claimed as Lean solver comparisons.
  unless sizedPositive > 0 && sizedNegative > 0 do
    throw "oracle fixture lacks sized and unsized type coverage"
  return (comparisons + autoTraitTrue + sizedPositive + sizedNegative,
    boxes, pointers, changedTails, sizedPositive, sizedNegative)

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then throw (IO.userError "usage: compare_structural_type_queries BASELINE.json [...]")
  for path in args do
    let source ← IO.FS.readFile path
    let decoded ← match readTypes source with
      | .ok decoded => pure decoded
      | .error error => throw (IO.userError s!"{path}: {error}")
    match check decoded with
    | .error error => throw (IO.userError s!"{path}: {error}")
    | .ok (count, boxes, pointers, tails, sizedPositive, sizedNegative) =>
      IO.println s!"{path}: {count} rustc/Lean structural query comparisons passed; Box={boxes}, raw_pointer={pointers}, nontrivial_tail={tails}, sized={sizedPositive}, unsized={sizedNegative}"
  return 0
