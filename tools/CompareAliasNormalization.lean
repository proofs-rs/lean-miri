import Miri.Input.AliasRuntime
import Miri.Input.Decoder
import Miri.Input.CompilerFacts

/-! Genuine checked-alias query comparison. Source RHS/clauses/impl heads drive
Lean; the retained rustc normalization row is oracle-only and is then removed
before a second run. The negative query uses the same declaration and raw impl
catalog, with u32 lacking the fixture's Gate implementation. -/
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
    throw "alias oracle reader requires canonical-main schema12"
  let definitions ← (← raw.getObjVal? "definitions").getArr?
  let nodes ← (← raw.getObjVal? "types").getArr?
  let mut matching := #[]
  for node in nodes do
    let shape ← node.getObjVal? "shape"
    unless (← (← shape.getObjVal? "kind").getStr?) == "alias" do continue
    let payload ← shape.getObjVal? "alias_payload"
    unless (← (← payload.getObjVal? "kind").getStr?) == "Free" do continue
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
      | _ => throw "focused alias oracle expects a primitive result"
    matching := matching.push result
  unless matching.size == 1 do throw "focused alias oracle needs exactly one matching instantiation"
  let some result := matching[0]? | throw "alias oracle result absent"
  pure result

def main (args : List String) : IO Unit := do
  let (baseline,path,negativeControl) ← match args with
    | [baseline,path] => pure (baseline,path,true)
    | [baseline,path,"--projection-bound"] => pure (baseline,path,false)
    | _ => throw (IO.userError "expected baseline12.json candidate13.json [--projection-bound]")
  let oracle ← IO.FS.readFile baseline
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let context ← must (AliasRuntime.Context.ofDocument decoded.document)
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let program ← must (lowerProgram decoded.document)
  let compiler ← must (CompilerFacts.ofProgram runtime program)
  let mut comparisons := 0
  let mut selected : Option TypeNode := none
  for node in decoded.document.types do
    let .alias .free false definition _ := node.shape | continue
    let some facts := node.compilerFacts | throw (IO.userError "alias source facts absent")
    check (!(facts.typeQueries.any (·.1 == "normalized"))) "producer retained eager free-alias normalization answer"
    let identity ← must (GenericInstantiation.identity context.generic definition)
    let expected ← must (oracleResult oracle identity)
    let actualId ← must (AliasRuntime.normalizeType context 256 10000 node.id)
    let integrated ← must (CompilerFacts.requiredType compiler node.id "normalized")
    check (integrated == actualId) "production compiler normalizer did not use raw free-alias algorithm"
    for query in #["is_freeze", "is_unpin", "is_unsafe_unpin"] do
      let answer ← must (CompilerFacts.boolean compiler node.id query)
      check answer s!"primitive checked-alias {query} failed shared normalization"
    let actual ← must (GenericInstantiation.ofType context.generic 256 actualId)
    check (actual == expected) s!"checked alias type{node.id}: Lean differs from independent rustc oracle"
    selected := some node
    comparisons := comparisons + 1
  check (comparisons > 0) "fixture did not retain checked free alias"
  let erasedOracle := {decoded.document with types := decoded.document.types.map fun node =>
    {node with compilerFacts := node.compilerFacts.map fun facts =>
      {facts with typeQueries := facts.typeQueries.filter (·.1 != "normalized")}}}
  let independent ← must (AliasRuntime.Context.ofDocument erasedOracle)
  let some selectedNode := selected | throw (IO.userError "checked alias control absent")
  let expected ← must (AliasRuntime.normalizeType context 256 10000 selectedNode.id)
  let withoutAnswers ← must (AliasRuntime.normalizeType independent 256 10000 selectedNode.id)
  check (withoutAnswers == expected) "normalizer consumed a closed rustc normalization answer"
  if negativeControl then
    let .alias .free false definition _ := selectedNode.shape | throw (IO.userError "alias source invariant")
    let identity ← must (GenericInstantiation.identity independent.generic definition)
    let u32 ← must (GenericInstantiation.ofType independent.generic 256 erasedOracle.queries.primitives.u32)
    let query := GenericSubstitution.Term.definition .type "alias_free_not_rigid" identity
      (GenericSubstitution.Terms.ofArray #[u32])
    match AliasRuntime.normalizeTerm independent 10000 256 #[] #[] query with
    | .ok _ => throw (IO.userError "unimplemented Gate<u32> own bound was ignored")
    | .error error =>
      check (error == "alias normalization own predicates have no solution")
        s!"negative alias query did not reach a definite trait no-solution: {error}"
  else
    let mut changed := 0
    let .alias .free false definitionId _ := selectedNode.shape
      | throw (IO.userError "checked alias source invariant")
    let identity ← must (GenericInstantiation.identity independent.generic definitionId)
    let definitions := independent.generic.definitions.map fun definition =>
      if (⟨definition.crateIndex,definition.index⟩ : GenericSubstitution.DefinitionIdentity) != identity then definition
      else {definition with sourceEnvironment := definition.sourceEnvironment.map fun material =>
        {material with ownPredicates := material.ownPredicates.map fun clause =>
          match clause.predicate with
          | .projection .projectionType definition arguments _ =>
            {clause with predicate := (.projection .projectionType definition arguments (.atom .type "uint" "u16"))}
          | _ => clause}}
    for definition in independent.generic.definitions do
      unless (⟨definition.crateIndex,definition.index⟩ : GenericSubstitution.DefinitionIdentity) == identity do continue
      if let some material := definition.sourceEnvironment then
        for clause in material.ownPredicates do
          if let .projection .projectionType .. := clause.predicate then changed := changed + 1
    check (changed == 1) "projection-bound control requires exactly one raw projection clause"
    let mismatched := {independent with generic := {independent.generic with definitions}}
    match AliasRuntime.normalizeType mismatched 256 10000 selectedNode.id with
    | .ok _ => throw (IO.userError "mismatched associated type equality bound was ignored")
    | .error error =>
      check (error == "alias normalization own predicates have no solution")
        s!"projection equality mismatch did not produce definite no-solution: {error}"
  IO.println s!"PASS {comparisons} checked free-alias normalization queries equal independent rustc; eager rows absent; dependent production auto traits passed"
