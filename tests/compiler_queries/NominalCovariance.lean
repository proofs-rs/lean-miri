import Miri.Input.CompilerCovariance
import Miri.Input.GenericInstantiationWorld
import Miri.Input.TableTail

open Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected raw source and nominal covariance oracle")
  let raw ← must (Lean.Json.parse (← IO.FS.readFile sourcePath))
  let definitions ← (← must ((← must (raw.getObjVal? "definitions")).getArr?)).mapM fun row => do
    let fields ← must row.getObj?
    let retained := fields.toList.filter fun field =>
      ["crate","index","generic_template","adt_declaration","alias_declaration","source_environment"].contains field.1
    must (JsonReader.run (DecoderValues.parseDefinitionId "$.definitions") (Lean.Json.mkObj retained).compress)
  let oracle ← must (Lean.Json.parse (← IO.FS.readFile oraclePath))
  let root ← must (oracle.getObjVal? "root")
  let identity : GenericSubstitution.DefinitionIdentity := ⟨
    ← must ((← must (root.getObjVal? "crate")).getNat?),
    ← must ((← must (root.getObjVal? "index")).getNat?)⟩
  let source ← must (VarianceMaterial.definition definitions identity)
  let some signature := source.genericTemplate.bind (·.signatureExpression)
    | throw (IO.userError "raw nominal fixture signature absent")
  let .binder variables (.node .aggregate "signature" _ terms) := signature
    | throw (IO.userError "raw nominal fixture signature shape")
  unless variables.isEmpty do throw (IO.userError "unexpected fixture signature binder")
  let rec values : GenericSubstitution.Terms → Array GenericSubstitution.Term
    | .nil => #[] | .cons term rest => #[term] ++ values rest
  let inputs := (values terms).pop
  unless inputs.size == 16 do throw (IO.userError "incomplete nominal fixture inputs")
  let mut world ← must (TypeArena.World.ofMaterial #[] #[] definitions #[] 8)
  let mut types := #[]
  for input in inputs do
    let (id,after) ← must ((GenericInstantiationWorld.resolveType 16384 input) world)
    world := after; types := types.push id
  let rows ← must ((← must (oracle.getObjVal? "relations")).getArr?)
  unless rows.size == 256 do throw (IO.userError "incomplete nominal covariance matrix")
  for row in rows do
    let left ← must ((← must (row.getObjVal? "left")).getNat?)
    let right ← must ((← must (row.getObjVal? "right")).getNat?)
    let expected ← must ((← must (row.getObjVal? "value")).getBool?)
    let some left := types[left]? | throw (IO.userError "nominal oracle left index")
    let some right := types[right]? | throw (IO.userError "nominal oracle right index")
    unless (← must (CompilerCovariance.relationInWorld {} world left right)) == expected do
      throw (IO.userError s!"independent nominal covariance mismatch: {left}/{right}")
  let some first := types[0]? | throw (IO.userError "nominal fixture first type absent")
  let .constructed (.adt nominal arguments) ← must (world.lookupType first)
    | throw (IO.userError "nominal fixture first type was not constructed")
  let missing : Except String Bool := do
    let definitions := definitions.filter fun source =>
      source.crateIndex != nominal.crateIndex || source.index != nominal.index
    let world ← TypeArena.World.ofMaterial #[] #[] definitions #[] 8
    let (left,world) ← (GenericInstantiationWorld.resolveType 16384 (inputs[0]?.getD (.atom .type "bool" ""))) world
    let (right,world) ← (GenericInstantiationWorld.resolveType 16384 (inputs[1]?.getD (.atom .type "bool" ""))) world
    CompilerCovariance.relationInWorld {} world left right
  if missing.isOk then throw (IO.userError "missing raw variance declaration accepted")
  let (malformed,after) ← must ((TypeArena.World.internType (.adt nominal (arguments ++ arguments))) world)
  if (CompilerCovariance.relationInWorld {} after first malformed).isOk then
    throw (IO.userError "malformed nominal argument arity accepted")
  if (CompilerCovariance.structural world 0 first (types[1]?.getD world.typeCount)).isOk then
    throw (IO.userError "nominal covariance fuel exhaustion accepted")
  IO.println "PASS 256 actual nominal covariance relations from raw declarations and empty type/constant/answer prefixes"
