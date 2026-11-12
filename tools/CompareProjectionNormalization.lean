import Miri.Input.AliasRuntime
import Miri.Input.Decoder
import Miri.Input.CompilerFacts

/-! Genuine projection normalization from raw selected impl RHS and clauses.
The independent canonical-main normalization row is read only by the oracle;
all candidate normalization rows are removed before the Lean algorithm runs. -/
open Lean Miri.Input
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

/-- Focused primitive-result oracle reader. Old alias rigidity is not present in
schema12 and is never guessed; only the alias's physical declaration identity
and its recorded primitive normalization result are observed here. -/
private def oracleResult (text : String) (identity : GenericSubstitution.DefinitionIdentity) :
    Except String GenericSubstitution.Term := do
  let raw ← Json.parse text
  unless (← (← raw.getObjVal? "schema_version").getNat?) == 12 do
    throw "projection oracle reader requires canonical-main schema12"
  let definitions ← (← raw.getObjVal? "definitions").getArr?
  let nodes ← (← raw.getObjVal? "types").getArr?
  let mut matching := #[]
  for node in nodes do
    let shape ← node.getObjVal? "shape"
    unless (← (← shape.getObjVal? "kind").getStr?) == "alias" do continue
    let payload ← shape.getObjVal? "alias_payload"
    unless (← (← payload.getObjVal? "kind").getStr?) == "Projection" do continue
    let id ← (← shape.getObjVal? "def_id").getNat?
    let some definition := definitions[id]? | throw "oracle alias definition absent"
    unless (← (← definition.getObjVal? "crate").getNat?) == identity.crateIndex &&
        (← (← definition.getObjVal? "index").getNat?) == identity.index do continue
    let facts ← node.getObjVal? "compiler_facts"
    let target ← (← (← facts.getObjVal? "type_queries").getObjVal? "normalized").getNat?
    let some target := nodes[target]? | throw "oracle normalized type absent"
    let shape ← target.getObjVal? "shape"
    let tag ← (← shape.getObjVal? "kind").getStr?
    let result ← match tag with
      | "uint" => do
        let kind ← (← shape.getObjVal? "unsigned_kind").getStr?
        pure (GenericSubstitution.Term.atom .type "uint" kind)
      | "int" => do
        let kind ← (← shape.getObjVal? "signed_kind").getStr?
        pure (GenericSubstitution.Term.atom .type "int" kind)
      | "bool" | "char" | "str" | "never" => pure (.atom .type tag "")
      | _ => throw "focused projection oracle expects a primitive result"
    matching := matching.push result
  unless matching.size == 1 do throw "focused projection oracle needs exactly one matching instantiation"
  let some result := matching[0]? | throw "projection oracle result absent"
  pure result

def main (args : List String) : IO Unit := do
  let (baseline,path,gatControls,specializationBoundary) ← match args with
    | [baseline,path] => pure (baseline,path,false,false)
    | [baseline,path,"--gat-controls"] => pure (baseline,path,true,false)
    | [baseline,path,"--specialization-boundary"] => pure (baseline,path,false,true)
    | _ => throw (IO.userError "expected baseline12.json candidate13.json [--gat-controls|--specialization-boundary]")
  let oracle ← IO.FS.readFile baseline
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let source := {decoded.document with types := decoded.document.types.map fun node =>
    {node with compilerFacts := node.compilerFacts.map fun facts =>
      {facts with typeQueries := facts.typeQueries.filter (·.1 != "normalized")}}}
  let context ← must (AliasRuntime.Context.ofDocument source)
  let runtime ← must ((RuntimeMetadata.ofDocument source).mapError toString)
  let program ← must (lowerProgram source)
  let compiler ← must (CompilerFacts.ofProgram runtime program)
  let mut comparisons := 0
  for node in source.types do
    let .alias .projection false definition _ := node.shape | continue
    let some exported := decoded.document.types[node.id]?
      | throw (IO.userError "projection material node absent")
    let some facts := exported.compilerFacts | throw (IO.userError "projection source facts absent")
    check (!(facts.typeQueries.any (·.1 == "normalized")))
      "producer retained eager nonrigid projection normalization answer"
    let identity ← must (GenericInstantiation.identity context.generic definition)
    let expected ← must (oracleResult oracle identity)
    if specializationBoundary then
      match AliasRuntime.normalizeType context 256 10000 node.id with
      | .ok _ => throw (IO.userError "specialization boundary silently selected an impl")
      | .error error =>
        check (error == "trait selection is ambiguous: multiple applicable impl candidates require specialization")
          s!"specialization boundary failed for an unrelated reason: {error}"
      match CompilerFacts.requiredType compiler node.id "normalized" with
      | .ok _ => throw (IO.userError "production specialization boundary returned a normalized answer")
      | .error error =>
        check (error == "trait selection is ambiguous: multiple applicable impl candidates require specialization")
          s!"production specialization boundary failed for an unrelated reason: {error}"
      comparisons := comparisons + 1
      continue
    let actualId ← must (AliasRuntime.normalizeType context 256 10000 node.id)
    let integrated ← must (CompilerFacts.requiredType compiler node.id "normalized")
    check (integrated == actualId) "production compiler normalizer did not use raw projection algorithm"
    let actual ← must (GenericInstantiation.ofType context.generic 256 actualId)
    check (actual == expected) s!"projection type{node.id}: Lean differs from independent rustc oracle"
    if gatControls then
      let term ← must (GenericInstantiation.ofType context.generic 256 node.id)
      let .definition .type tag identity children := term
        | throw (IO.userError "GAT query must retain alias definition")
      let arguments := AliasNormalization.termsToArray children
      check (arguments.size == 2) "GAT fixture requires Self plus own type argument"
      let negative := GenericSubstitution.Term.definition .type tag identity
        (GenericSubstitution.Terms.ofArray (arguments.set! 1 (.atom .type "uint" "u32")))
      match AliasRuntime.normalizeTerm context 10000 256 #[] #[] negative with
      | .ok _ => throw (IO.userError "GAT own argument obligation was ignored")
      | .error error =>
        check (error == "alias normalization own predicates have no solution")
          s!"GAT own clause did not produce definite no-solution: {error}"
    comparisons := comparisons + 1
  check (comparisons > 0) "fixture did not retain projection alias"
  if specializationBoundary then
    IO.println s!"PASS {comparisons} genuine rustc specialization queries rejected explicitly at the unported specialization boundary"
  else
    IO.println s!"PASS {comparisons} projection normalization queries equal independent rustc; all eager normalization rows removed before Lean execution"
