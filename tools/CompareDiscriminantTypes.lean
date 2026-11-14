import Miri.Input.StructuralDiscriminantType
import Miri.Input.CompilerFacts
import Miri.Input.Decoder
open Lean Miri.Input
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def keyOfShape (shape : Json) : Except String String := do
  match ← (← shape.getObjVal? "kind").getStr? with
  | "uint" => (← shape.getObjVal? "unsigned_kind").getStr?
  | "int" => (← shape.getObjVal? "signed_kind").getStr?
  | _ => throw "discriminant oracle result must be integer"
private def oracleEnums (text : String) : Except String (Array (GenericSubstitution.DefinitionIdentity × String)) := do
  let raw ← Json.parse text
  unless (← (← raw.getObjVal? "schema_version").getNat?) == 12 do throw "requires independent canonical schema12 oracle"
  let nodes ← (← raw.getObjVal? "types").getArr?
  let definitions ← (← raw.getObjVal? "definitions").getArr?
  let mut result := #[]
  for node in nodes do
    let shape ← node.getObjVal? "shape"
    unless (← (← shape.getObjVal? "kind").getStr?) == "adt" do continue
    unless (← (← shape.getObjVal? "adt_kind").getStr?) == "enum" do continue
    let definition ← (← shape.getObjVal? "def_id").getNat?
    let some definition := definitions[definition]? | throw "oracle enum definition absent"
    let identity : GenericSubstitution.DefinitionIdentity := ⟨
      ← (← definition.getObjVal? "crate").getNat?, ← (← definition.getObjVal? "index").getNat?⟩
    if identity.crateIndex != 0 then continue
    let queries ← (← node.getObjVal? "compiler_facts").getObjVal? "type_queries"
    let target ← (← queries.getObjVal? "discriminant_type").getNat?
    let some target := nodes[target]? | throw "oracle discriminant type absent"
    result := result.push (identity,← keyOfShape (← target.getObjVal? "shape"))
  pure result

def main (args : List String) : IO Unit := do
  let [baseline,candidate] := args | throw (IO.userError "expected baseline12.json candidate13.json")
  let oracle ← must (oracleEnums (← IO.FS.readFile baseline))
  let decoded ← must (decodeJson (← IO.FS.readFile candidate))
  for node in decoded.document.types do
    if let some facts := node.compilerFacts then
      if facts.typeQueries.any (·.1 == "discriminant_type") then
        throw (IO.userError "producer retained eager discriminant type result")
  let source := {decoded.document with types := decoded.document.types.map fun node =>
    {node with compilerFacts := node.compilerFacts.map fun facts =>
      {facts with typeQueries := facts.typeQueries.filter (·.1 != "discriminant_type")}}}
  let runtime ← must ((RuntimeMetadata.ofDocument source).mapError toString)
  let compiler ← must (CompilerFacts.ofProgram runtime (← must (lowerProgram source)))
  let hooks : StructuralDiscriminantType.Hooks := {
    shape := fun id => return (← runtime.node id |>.mapError toString).shape,
    primitive := fun key => return (← CompilerPrimitiveFacts.primitiveLayout runtime key).ty,
    normalizeAlias := fun _ id => CompilerFacts.requiredType compiler id "normalized",
    eraseUnsafeBinder := fun id => CompilerFacts.requiredType compiler id "unsafe_binder_erased" }
  let mut comparisons := 0
  for node in decoded.document.types do
    let .adt data := node.shape | continue
    unless data.kind == .enumKind do continue
    let some definition := decoded.document.definitions[data.definition]?
      | throw (IO.userError "candidate enum definition absent")
    let identity : GenericSubstitution.DefinitionIdentity := ⟨definition.crateIndex,definition.index⟩
    if identity.crateIndex != 0 then continue
    let expected := oracle.filter (·.1 == identity)
    unless expected.size == 1 do throw (IO.userError "enum oracle physical identity missing or duplicated")
    let some (_,key) := expected[0]? | throw (IO.userError "enum oracle result absent")
    let expected ← must (hooks.primitive key)
    let actual ← must (StructuralDiscriminantType.query hooks 256 node.id)
    unless actual == expected do throw (IO.userError "structural enum discriminant type differs from independent rustc")
    let integrated ← must (CompilerFacts.requiredType compiler node.id "discriminant_type")
    unless integrated == actual do throw (IO.userError "production discriminant type query did not use structural provider")
    comparisons := comparisons + 1
  unless comparisons == 6 do throw (IO.userError "fixture requires six enum representation cases")
  let badSource := {runtime.source with queries := {runtime.source.queries with
    primitives := {runtime.source.queries.primitives with u8 := runtime.source.queries.primitives.u16}}}
  let badRuntime := {runtime with source := badSource}
  match CompilerPrimitiveFacts.primitiveType badRuntime "u8" with
  | .ok _ => throw (IO.userError "mislabeled primitive anchor was accepted")
  | .error error =>
    unless error == "compiler primitive type anchor mismatch: u8" do
      throw (IO.userError s!"primitive anchor control failed for unrelated reason: {error}")
  IO.println s!"PASS {comparisons} structural discriminant type answers equal independent rustc, including repr(C) public isize versus physical tag"
