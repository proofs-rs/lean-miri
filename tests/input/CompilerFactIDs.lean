import Miri.Input.CompilerFacts
import Miri.Input.CompilerDiscriminantFacts

open Lean Miri Miri.Input

private def must (result : Except ε α) [ToString ε] : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

private def equalResult [DecidableEq α] (expected actual : Except String α) : IO Unit :=
  match expected, actual with
  | .ok expected, .ok actual =>
    unless decide (expected = actual) do throw (IO.userError "compiler query result changed")
  | .error _, .error _ => pure ()
  | _, _ => throw (IO.userError "compiler query success/failure changed")

private def sourceQuery (catalog : Reader.Catalog) (facts : Json) (key name : String) : Except String Json := do
  catalog.field (← catalog.field facts key "facts") name "query"
private def available (catalog : Reader.Catalog) (query : Json) : Except String Json := do
  unless (← catalog.string (← catalog.field query "status" "query") "query") == "supported" do throw "query unavailable"
  catalog.inspect (← catalog.field query "value" "query") "value"

private def wireId (catalog : Reader.Catalog) (raw : Json) (actual : Nat) : IO Unit := do
  if let some id ← must (catalog.sharedId? raw "query") then
    unless id == actual do throw (IO.userError "query wire ID changed")

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: CompilerFactIDs <export.json>")
  let source ← IO.FS.readFile path
  let catalog ← must (Reader.Catalog.parse (← must (Json.parse source)))
  let rawTypes ← must (catalog.array (← must (catalog.field catalog.root "types" "$")) "types")
  let decoded ← must (decodeRuntimeJson source)
  let runtime ← must (RuntimeMetadata.ofDocument decoded.document)
  let program ← must (lowerCoreProgram decoded.document)
  let cleanSource := {runtime.source with
    raw := .null
    sharedNodes := #[]
    types := runtime.source.types }
  let context := CompilerFacts.ofOwner {(← must (RuntimeProgram.ofProgram program)) with input := cleanSource}
  let tables := runtime.source.compilerFactTables
  let mut booleans := 0
  let mut types := 0
  let mut discriminants := 0
  for (node,index) in runtime.source.types.toList.zipIdx do
    let some facts := node.compilerFacts | continue
    let some rawType := rawTypes[index]? | throw (IO.userError "raw type absent")
    let rawFacts ← must (catalog.field rawType "compiler_facts" "type")
    let raw := rawFacts
    wireId catalog (← must (catalog.field rawFacts "boolean_queries" "facts")) facts.booleanQueries
    wireId catalog (← must (catalog.field rawFacts "type_queries" "facts")) facts.typeQueries
    for (name,id) in ← must (tables.booleanQueries.lookup facts.booleanQueries) do
      let expected := do (← available catalog (← sourceQuery catalog raw "boolean_queries" name)).getBool?
      equalResult expected (CompilerFacts.boolean context node.id name)
      wireId catalog (← must (catalog.field (← must (catalog.field rawFacts "boolean_queries" "facts")) name "query")) id
      booleans := booleans + 1
    for (name,id) in ← must (tables.typeQueries.lookup facts.typeQueries) do
      let expected := do
        let value ← available catalog (← sourceQuery catalog raw "type_queries" name)
        if value == .null then pure none else some <$> value.getObjValAs? Nat "type_id"
      equalResult expected (CompilerFacts.optionalType context node.id name)
      wireId catalog (← must (catalog.field (← must (catalog.field rawFacts "type_queries" "facts")) name "query")) id
      types := types + 1
    if let .ok info := facts.discriminants then
      let expected ← must (available catalog (← must (catalog.field raw "discriminants" "facts")))
      unless info.hasDiscriminants == (← must (catalog.boolean (← must (catalog.field expected "has_discriminants" "discriminants")) "discriminants")) do
        throw (IO.userError "discriminant presence changed")
      let rawValues ← must (catalog.array (← must (catalog.field expected "values" "discriminants")) "discriminants")
      let ids ← must (tables.discriminantLists.lookup info.values)
      unless ids.size == rawValues.size do throw (IO.userError "discriminant count changed")
      for (id,index) in ids.toList.zipIdx do
        let value ← must (tables.discriminantValues.lookup id)
        let some raw := rawValues[index]? | throw (IO.userError "raw discriminant absent")
        let bits ← must (catalog.string (← must (catalog.field raw "bits" "discriminant")) "bits")
        unless some value.bits == bits.toNat? && value.variant == (← must (catalog.natural (← must (catalog.field raw "variant" "discriminant")) "variant")) &&
            value.typeId == (← must (catalog.natural (← must (catalog.field (← must (catalog.field raw "type" "discriminant")) "type_id" "type")) "type")) do
          throw (IO.userError "discriminant value changed")
        discriminants := discriminants + 1
  unless booleans > 0 && types > 0 && discriminants > 0 do throw (IO.userError "fixture lacks compiler queries")
  IO.println s!"compiler fact IDs: PASS ({booleans} boolean, {types} type queries, {discriminants} discriminants; wire IDs retained; raw source removed)"
