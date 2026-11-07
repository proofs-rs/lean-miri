import Miri.Input.CompilerVTableQueries
import Miri.Input.CompilerVirtualFacts

open Lean Miri Miri.Input

private def must (result : Except ε α) [ToString ε] : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

private def expectedIds (catalog : Reader.Catalog) (input : Json) : Except String (Array Nat) := do
  (← catalog.array input "predicates").mapM fun value => do
    catalog.natural (← catalog.field value "predicate_id" "predicate") "predicate"

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: PredicateIDs <export.json>")
  let source ← IO.FS.readFile path
  let catalog ← must (Reader.Catalog.parse (← must (Json.parse source)))
  let decoded ← must (decodeRuntimeJson source)
  let runtime ← must (RuntimeMetadata.ofDocument decoded.document)
  let program ← must (lowerCoreProgram decoded.document)
  let facts ← must (CompilerFactAdapters.prepare (← must (CompilerFacts.ofProgram program)))
  let cleanSource := {runtime.source with
    raw := .null
    sharedNodes := #[]
    types := runtime.source.types }
  let cleanContext : CompilerFacts.Context := {
    owner := {facts.context.owner with input := cleanSource} }
  let clean := {facts with context := cleanContext}
  let queries ← must (CompilerVTableQueries.prepare clean)
  let rawTypes ← must (catalog.array (← must (catalog.field catalog.root "types" "$")) "types")
  let rawDefinitions ← must ((← must (program.input.raw.getObjVal? "compiler_predicate_queries")).getArr?)
  let mut lists := 0
  let mut predicates := 0
  for (entry,id) in facts.dynamicPredicates.toList.zipIdx do
    let some list := entry | continue
    let actual ← must (CompilerVTableFacts.predicates clean id)
    unless actual.map (·.id) == list.values do throw (IO.userError "predicate ID changed")
    if let some raw := catalog.nodes[id]? then
      unless (← must (expectedIds catalog raw)) == list.values do throw (IO.userError "predicate wire list changed")
    else unless list.values.isEmpty do throw (IO.userError "nonempty inline predicate list")
    for predicate in actual do
      let some raw := rawDefinitions[predicate.id]? | throw (IO.userError "predicate definition absent")
      unless predicate.stableKey == (← must (raw.getObjValAs? Nat "stable_key")) &&
          predicate.autoTrait == (← must (raw.getObjValAs? Bool "auto_trait")) do
        throw (IO.userError "predicate comparison evidence changed")
      let normalization ← must (raw.getObjVal? "normalization")
      let expected := do
        unless (← normalization.getObjValAs? String "status") == "supported" do throw "unavailable"
        normalization.getObjValAs? Nat "value"
      match expected, CompilerVTableFacts.normalizePredicate clean predicate with
      | .ok expected, .ok actual => unless expected == actual do throw (IO.userError "normalized predicate changed")
      | .error _, .error _ => pure ()
      | _, _ => throw (IO.userError "predicate normalization availability changed")
      predicates := predicates + 1
    lists := lists + 1
  let mut dynamicTypes := 0
  for node in runtime.source.types do
    unless node.shapeKind == .dynamicTraitObject do continue
    let some value ← must (CompilerVirtualFacts.dynamicData clean node.id)
      | throw (IO.userError "dynamic data absent")
    let some raw := rawTypes[node.id]? | throw (IO.userError "dynamic type absent")
    let rawShape ← must (catalog.field raw "shape" "type")
    let ids ← must (expectedIds catalog (← must (catalog.field rawShape "predicates" "type")))
    let list ← must (clean.dynamicPredicates.lookup value.predicates)
    unless ids == list.values do throw (IO.userError "dynamic type predicate list changed")
    let principal ← must (catalog.inspect (← must (catalog.field rawShape "principal_predicate" "type")) "principal")
    let expected ← if principal == .null then pure none else some <$> must (principal.getObjValAs? Nat "predicate_id")
    unless value.principal == expected do throw (IO.userError "dynamic principal changed")
    dynamicTypes := dynamicTypes + 1
  let mut erasures := 0
  for row in program.input.vtableTables.queries do
    let row ← must row
    let actual ← must (CompilerVTableQueries.eraseAndAnonymize queries row.inputTypeId row.inputPredicates)
    unless actual == (row.outputTypeId,row.outputPredicates) do throw (IO.userError "vtable erasure result changed")
    erasures := erasures + 1
  unless predicates > 0 && dynamicTypes > 0 && erasures > 0 do throw (IO.userError "fixture lacks dynamic queries")
  IO.println s!"predicate IDs: PASS ({lists} lists; {predicates} predicates; {dynamicTypes} dynamic types; {erasures} erasure queries; raw source removed)"
