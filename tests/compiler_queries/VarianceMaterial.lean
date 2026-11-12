import Miri.Input.VarianceMaterial
import Miri.Input.TableTail

open Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

private def parseVariance : String → Except String Miri.MIR.Variance
  | "covariant" => pure .Covariant | "contravariant" => pure .Contravariant
  | "invariant" => pure .Invariant | "bivariant" => pure .Bivariant
  | other => throw s!"unknown compiler variance: {other}"

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath,latticePath] := args
    | throw (IO.userError "expected raw export, variance oracle and lattice oracle")
  -- Source-only comparison adapter: variance reads declaration identities,
  -- raw generic templates and ADT/alias roles, not execution catalogs or paths.
  let raw ← must (Lean.Json.parse (← IO.FS.readFile sourcePath))
  let sourceRows ← must ((← must (raw.getObjVal? "definitions")).getArr?)
  let definitions ← sourceRows.mapM fun row => do
    let fields ← must row.getObj?
    let retained := fields.toList.filter fun field =>
      ["crate","index","generic_template","adt_declaration","alias_declaration"].contains field.1
    must (JsonReader.run (DecoderValues.parseDefinitionId "$.definitions") (Lean.Json.mkObj retained).compress)
  let rows ← must ((← must (Lean.Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  unless rows.size == 15 do throw (IO.userError "incomplete variance oracle")
  for row in rows do
    let crateIndex ← must ((← must (row.getObjVal? "crate")).getNat?)
    let index ← must ((← must (row.getObjVal? "index")).getNat?)
    let name ← must ((← must (row.getObjVal? "name")).getStr?)
    let values ← must ((← must (row.getObjVal? "variances")).getArr?)
    let expected ← values.mapM fun value => do must (parseVariance (← must value.getStr?))
    let actual ← must (VarianceMaterial.query definitions ⟨crateIndex,index⟩)
    unless actual == expected do
      throw (IO.userError s!"raw declaration variance differs from rustc: {name}: {reprStr actual} / {reprStr expected}")
    let missing := definitions.filter fun value =>
      value.crateIndex != crateIndex || value.index != index
    if (VarianceMaterial.query missing ⟨crateIndex,index⟩).isOk then
      throw (IO.userError "missing raw variance declaration was accepted")
  let lattice ← must ((← must (Lean.Json.parse (← IO.FS.readFile latticePath))).getArr?)
  unless lattice.size == 16 do throw (IO.userError "incomplete rustc variance composition table")
  for row in lattice do
    let read := fun key => do
      let value ← must ((← must (row.getObjVal? key)).getStr?)
      must (parseVariance value)
    let outer ← read "outer"
    let inner ← read "inner"
    let expected ← read "result"
    unless VarianceInference.compose outer inner == expected do
      throw (IO.userError "variance composition differs from pinned rustc")
  let some first := rows[0]? | throw (IO.userError "variance oracle root absent")
  let rootCrate ← must ((← must (first.getObjVal? "crate")).getNat?)
  let rootIndex ← must ((← must (first.getObjVal? "index")).getNat?)
  let root : GenericSubstitution.DefinitionIdentity := ⟨rootCrate,rootIndex⟩
  let some function := definitions.find? (fun source =>
      source.genericTemplate.any (·.signatureExpression.isSome))
    | throw (IO.userError "function role source absent")
  let functionIdentity : GenericSubstitution.DefinitionIdentity := ⟨function.crateIndex,function.index⟩
  let parameter := GenericSubstitution.Term.parameter .type 0
  let badFields : Array GenericSubstitution.Term := #[
    .node .type "imaginary" "" .nil,
    .node .type "function_pointer" "" (#[parameter] : Array GenericSubstitution.Term),
    .node .type "tuple" "" (#[parameter,.node .type "imaginary" "" .nil] : Array GenericSubstitution.Term),
    .definition .type "alias_unknown_rigidity" root (#[parameter] : Array GenericSubstitution.Term),
    .definition .type "adt" functionIdentity .nil]
  for bad in badFields do
    let altered := definitions.map fun source =>
      if source.crateIndex == rootCrate && source.index == rootIndex then
        {source with genericTemplate := source.genericTemplate.map fun template =>
          {template with fields := template.fields.map fun field => {field with expression := bad}}}
      else source
    if (VarianceMaterial.query altered root).isOk then
      throw (IO.userError "malformed raw variance syntax or nominal declaration role accepted")
  IO.println "PASS 15 complete raw declaration variances, 16 composition pairs and missing-source controls"
