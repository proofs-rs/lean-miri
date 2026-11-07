import Miri.Input.RuntimeMetadata

open Lean Miri.Input

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: LayoutIDs <export.json>")
  let source ← IO.FS.readFile path
  let .ok json := Json.parse source | throw (IO.userError "JSON parse failed")
  let .ok catalog := Reader.Catalog.parse json | throw (IO.userError "catalog rejected")
  let decoded ← match decodeRuntimeJson source with
    | .ok decoded => pure decoded
    | .error error => throw (IO.userError error)
  let .ok rawTypes := catalog.array (← match catalog.field catalog.root "types" "$" with
      | .ok value => pure value | .error message => throw (IO.userError message)) "types"
    | throw (IO.userError "type rows missing")
  let mut shared : Std.HashSet Nat := {}
  let mut inlineCount := 0
  for (raw, index) in rawTypes.toList.zipIdx do
    let some node := decoded.document.types[index]? | throw (IO.userError "type row missing")
    let .ok layout := catalog.field raw "layout" "type" | throw (IO.userError "layout missing")
    let .ok id := catalog.sharedId? layout "layout" | throw (IO.userError "bad layout reference")
    match id with
    | some id =>
      unless node.layoutId == id do throw (IO.userError "shared layout ID changed")
      shared := shared.insert id
    | none =>
      unless node.layoutId >= catalog.nodes.size do throw (IO.userError "inline layout used a shared slot")
      inlineCount := inlineCount + 1
    let .ok _ := decoded.document.layoutTable.lookup node.layoutId
      | throw (IO.userError "referenced layout not constructed")
  let mut layouts : Std.HashSet Nat := {}
  for type in decoded.document.types do layouts := layouts.insert type.layoutId
  for field in decoded.document.projectionTables.fields do
    if let some field := field then layouts := layouts.insert field.layoutId
  for parent in decoded.document.projectionTables.parents do
    if let some parent := parent then layouts := layouts.insert parent.layoutId
  for argument in decoded.document.abiTables.arguments do
    if let some argument := argument then
      if let some id := argument.layoutId then layouts := layouts.insert id
  unless (decoded.document.layoutTable.filter (·.isSome)).size == layouts.size do
    throw (IO.userError "layout construction duplicated or omitted entries")
  let .ok metadata := RuntimeMetadata.ofDocument decoded.document
    | throw (IO.userError "runtime metadata rejected")
  let some first := decoded.document.types[0]? | throw (IO.userError "no source type")
  let unavailable := RuntimeMetadataError.invalid "test layout" "stored failure"
  if bound : first.layoutId < metadata.layouts.size then
    let edited := {metadata with layouts := metadata.layouts.set first.layoutId (some (.error unavailable)) bound}
    unless decide (edited.lookup first.id = .error unavailable) do
      throw (IO.userError "runtime lookup did not consume the shared layout slot")
    let missing := {metadata with layouts := metadata.layouts.set first.layoutId none bound}
    match missing.lookup first.id with
    | .error (.invalid ..) => pure ()
    | _ => throw (IO.userError "missing layout slot accepted")
  else throw (IO.userError "runtime layout table too short")
  IO.println s!"layout IDs: PASS ({rawTypes.size} types; {shared.size} shared layouts)"
