import Miri.Input.RuntimeMetadata

open Lean Miri Miri.Input

private def must (result : Except ε α) [ToString ε] : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

private def same (left right : RuntimeMetadata.Result (ABI.TyAndLayout TypeId)) : IO Unit :=
  match left, right with
  | .ok left, .ok right =>
    unless left == right do throw (IO.userError "typed relationship changed")
  | .error _, .error _ => pure ()
  | _, _ => throw (IO.userError "typed relationship success/failure changed")

private def checkValidation : IO Unit := do
  let reference := Json.mkObj [("$lean_miri_shared_ref", toJson (0 : Nat))]
  let make := fun target => Json.mkObj [
    ("shared_payloads", Json.mkObj [("schema_version", toJson (2 : Nat)),
      ("nodes", Json.arr #[Json.arr #[Json.mkObj [("type_id", toJson target)]]])]),
    ("types", Json.arr #[Json.mkObj [("type_id", toJson (0 : Nat)), ("shape", Json.mkObj [
      ("status", .str "supported"), ("kind", .str "tuple"), ("elements", reference)])]])]
  let valid ← must (Reader.Catalog.parse (make (0 : Nat)))
  let (relations, tables) ← must valid.readTypeRelations
  unless relations[0]?.bind (·.elements) == some 0 do
    throw (IO.userError "tuple shared ID changed")
  unless (← must (tables.typeLists.lookup 0)) == #[0] do
    throw (IO.userError "tuple type ID changed")
  let invalid ← must (Reader.Catalog.parse (make (1 : Nat)))
  match invalid.readTypeRelations with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "out-of-range type reference accepted")

def main (args : List String) : IO Unit := do
  checkValidation
  let some path := args.head? | throw (IO.userError "usage: TypeRelationIDs <export.json>")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let runtime ← must (RuntimeMetadata.ofDocument decoded.document)
  let cleanSource := {runtime.source with raw := .null, sharedNodes := #[], types := runtime.source.types.map fun node =>
    {node with compilerFacts := node.compilerFacts.map fun facts =>
      {facts with projectionQuery := none}}}
  let clean := {runtime with source := cleanSource}
  let tables := clean.source.typeRelationTables
  let mut fields := 0
  let mut pointers := 0
  let mut tuples := 0
  for node in clean.source.types do
    if let some id := node.relations.pointee then
      if let .ok parent := clean.lookup node.id then
        same (clean.pointee parent) (clean.lookup id)
        pointers := pointers + 1
    if let some id := node.relations.elements then
      let elements ← must (tables.typeLists.lookup id)
      same (clean.tupleLayout elements) (runtime.tupleLayout elements)
      tuples := tuples + 1
      if let .ok parent := clean.lookup node.id then
        for (typeId, index) in elements.toList.zipIdx do
          same (clean.field parent index) (clean.lookup typeId)
          fields := fields + 1
    if let some typeId := node.relations.element then
      if let .ok parent := clean.lookup node.id then
        same (clean.field parent 0) (clean.lookup typeId)
        fields := fields + 1
    if let some id := node.relations.variants then
      for id in ← must (tables.variantLists.lookup id) do
        let variant ← must (tables.variants.lookup id)
        let ids ← must (tables.fieldLists.lookup variant.fields)
        if let .ok parent := clean.lookup node.id then
          if let .ok parent := clean.forVariant parent variant.index then
            for (id, index) in ids.toList.zipIdx do
              let field ← must (tables.fields.lookup id)
              unless field.index == index do throw (IO.userError "non-positional field")
              same (clean.field parent index) (clean.lookup field.typeId)
              fields := fields + 1
  unless fields > 0 && pointers > 0 && tuples > 0 do
    throw (IO.userError "fixture lacks type relationships")
  IO.println s!"type relation IDs: PASS ({fields} fields; {pointers} pointers; {tuples} tuples; raw source removed)"
