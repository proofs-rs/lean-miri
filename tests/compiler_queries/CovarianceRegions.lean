import Miri.Input.CompilerCovariance
import Miri.Input.TableTail
import Miri.Input.TypeConstCodec

open Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected independent covariance baseline source")
  let raw ← must (Lean.Json.parse (← IO.FS.readFile path))
  let definitions ← (← must ((← must (raw.getObjVal? "definitions")).getArr?)).mapM fun row => do
    let fields ← must row.getObj?
    let retained := fields.toList.filter fun field =>
      ["crate","index","generic_template","adt_declaration","alias_declaration","source_environment"].contains field.1
    must (JsonReader.run (DecoderValues.parseDefinitionId "$.definitions") (Lean.Json.mkObj retained).compress)
  let booleans ← (← must ((← must (raw.getObjVal? "boolean_queries")).getArr?)).mapM fun row =>
    must (JsonReader.run DecoderValues.booleanQueries row.compress)
  let discriminants ← (← must ((← must (raw.getObjVal? "discriminants")).getArr?)).mapM fun row =>
    must (JsonReader.run (DecoderValues.parseDiscriminants "$.discriminants") row.compress)
  let types ← (← must ((← must (raw.getObjVal? "types")).getArr?)).mapM fun row =>
    must (JsonReader.run (DecoderValues.parseTypeNode "$.types" booleans discriminants) row.compress)
  let constants ← (← must ((← must (raw.getObjVal? "type_constants")).getArr?)).mapM fun row =>
    must (JsonReader.run (TypeConstCodec.decode "$.type_constants") row.compress)
  let world ← must (TypeArena.World.ofMaterial types constants definitions 8)
  let rows ← must ((← must (raw.getObjVal? "compiler_covariance_queries")).getArr?)
  unless rows.size == 8 do throw (IO.userError "expected eight actual static/erased baseline relations")
  for row in rows do
    let left ← must ((← must (row.getObjVal? "source_type")).getNat?)
    let right ← must ((← must (row.getObjVal? "target_type")).getNat?)
    let expected ← must ((← must (row.getObjVal? "value")).getBool?)
    unless (← must (CompilerCovariance.relationInWorld {} world left right)) == expected do
      throw (IO.userError "static/erased covariance differs from actual compiler baseline")
  IO.println "PASS eight actual static/erased covariance relations with an empty answer catalog"
