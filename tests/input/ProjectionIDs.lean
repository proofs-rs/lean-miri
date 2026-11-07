import Miri.Input.RuntimeMetadata

open Lean Miri Miri.Input

private def must (result : Except ε α) [ToString ε] : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: ProjectionIDs <export.json>")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let metadata ← must (RuntimeMetadata.ofDocument decoded.document)
  let types := decoded.document.types
  let clean := {metadata with source := {metadata.source with raw := .null, types := types}}
  let tables := decoded.document.projectionTables
  let mut parents := 0
  let mut fields := 0
  let mut variants := 0
  for type in types do
    let some facts := type.compilerFacts | continue
    let some queryId := facts.projectionQuery | continue
    let query ← must (tables.queries.lookup queryId |>.mapError (fun id => s!"query {id} missing"))
    unless query.status == .supported do continue
    let some valueId := query.value | continue
    let value ← must (tables.values.lookup valueId |>.mapError (fun id => s!"value {id} missing"))
    let records ← must (tables.parentLists.lookup value.parents |>.mapError (fun id => s!"parent list {id} missing"))
    for recordId in records do
      let record ← must (tables.parents.lookup recordId |>.mapError (fun id => s!"parent {id} missing"))
      let layout ← must (← must (metadata.layouts.lookup record.layoutId |>.mapError (fun id => s!"layout {id} missing")))
      let parent : ABI.TyAndLayout TypeId := ⟨type.id, layout⟩
      let entries ← must (tables.fieldLists.lookup record.fields |>.mapError (fun id => s!"field list {id} missing"))
      parents := parents + 1
      for (fieldId, index) in entries.toList.zipIdx do
        let field ← must (tables.fields.lookup fieldId |>.mapError (fun id => s!"field {id} missing"))
        let expected ← must (← must (metadata.layouts.lookup field.layoutId |>.mapError (fun id => s!"layout {id} missing")))
        let actual ← must (clean.field parent index)
        unless actual.ty == field.typeId && actual.layout == expected do
          throw (IO.userError s!"type {type.id}: field {index} changed")
        if type.shapeKind == .str then
          let arbitrary ← must (clean.field parent 99)
          unless arbitrary == actual do throw (IO.userError "str field index special case changed")
        fields := fields + 1
      if let some index := record.variant then
        let actual ← must (clean.forVariant (← must (clean.lookup type.id)) index)
        unless actual == parent do throw (IO.userError s!"type {type.id}: variant {index} changed")
        variants := variants + 1
  unless parents > 0 && fields > 0 && variants > 0 do throw (IO.userError "fixture did not exercise projection queries")
  IO.println s!"projection IDs: PASS ({parents} parents; {fields} fields; {variants} variants; raw payloads erased)"
