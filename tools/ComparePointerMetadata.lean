import Miri.Input.TableCore
import Miri.Input.StructuralPointerMetadata

/-! Category reader over a fresh canonical-main rustc export. Its normalization
rows supply the still-residual normalization dependency; dynamic rows supply the
still-residual DynMetadata<Self> constructor. Neither is counted as an algorithm
port. Unit/usize metadata selection and structural tail traversal run in Lean.
No production reader imports or adapts the old wire schema. -/
open Miri.Input

private def check (text : String) : Except String (Nat × Nat × Nat) := do
  let raw ← Lean.Json.parse text
  unless (← (← raw.getObjVal? "schema_version").getNat?) == 12 do
    throw "pointer metadata oracle requires canonical-main schema12"
  let pool ← JsonReader.run (JsonReader.array DecoderValues.booleanQueries)
    (← raw.getObjVal? "boolean_queries").compress
  let discriminants ← JsonReader.run (JsonReader.array DecoderValues.parseDiscriminants)
    (← raw.getObjVal? "discriminants").compress
  let rows ← (← raw.getObjVal? "types").getArr?
  -- Schema12 did not retain alias rigidity. Keep those query dependency rows,
  -- but never invent a TypeShape alias flag: normalization must reach a known
  -- non-alias source shape before this category inspects a tail.
  let nodes ← rows.mapM fun row => do
    if (← (← (← row.getObjVal? "shape").getObjVal? "kind").getStr?) == "alias" then
      pure (none : Option TypeNode)
    else return some (← JsonReader.run
      (DecoderValues.parseTypeNode "$oracle.types" pool discriminants) row.compress)
  let rawQuery (id : Nat) (key : String) : Except String Nat := do
    let some row := rows[id]? | throw "oracle query row absent"
    let facts ← row.getObjVal? "compiler_facts"
    (← (← facts.getObjVal? "type_queries").getObjVal? key).getNat?
  let primitives ← raw.getObjVal? "compiler_runtime_primitives"
  let unit ← (← primitives.getObjVal? "unit").getNat?
  let usize ← (← primitives.getObjVal? "usize").getNat?
  let lookup (id : Nat) : Except String TypeNode := do
    let some (some value) := nodes[id]? | throw "oracle type shape unavailable (alias rigidity not retained)"
    unless value.id == id do throw "oracle type ID/index mismatch"
    pure value
  let oracle := rawQuery
  unless (match (← lookup unit).shape with | .tuple fields => fields.isEmpty | _ => false) do
    throw "oracle unit material is not empty tuple"
  unless (← lookup usize).shapeMetadata.unsignedKind == some (.known .usize) do
    throw "oracle usize material has wrong primitive kind"
  let mut units := 0
  let mut sizes := 0
  let mut dynamicResidual := 0
  for id in [:rows.size] do
    let choice ← StructuralPointerMetadata.query (fun id => return (← lookup id).shape)
      (fun id => oracle id "normalized") (rows.size + 1) id
    let actual ← match choice with
      | .unit => units := units + 1; pure unit
      | .usize => sizes := sizes + 1; pure usize
      | .dynamic tail => dynamicResidual := dynamicResidual + 1; oracle tail "pointer_metadata_type"
      | .unresolved tail => throw s!"unresolved metadata tail {tail}"
    let expected ← oracle id "pointer_metadata_type"
    unless actual == expected do
      throw s!"pointer metadata differs from rustc for type{id}: actual{actual},expected{expected}"
  unless units > 0 && sizes > 0 && dynamicResidual > 0 do
    throw "metadata fixture lacks unit,usize or residual dynamic branches"
  return (units,sizes,dynamicResidual)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected canonical-main baseline export")
  let result ← match check (← IO.FS.readFile path) with
    | .ok value => pure value | .error error => throw (IO.userError error)
  let (units,sizes,dynamicResidual) := result
  IO.println s!"PASS {units + sizes} computed unit/usize pointer metadata selections equal pinned rustc; {dynamicResidual} dynamic constructor residuals checked separately"
