import MiriTests.Input.SharedPayloads
import Miri.Input.Reader.Places
import Miri.Input.RuntimeMetadata
import Miri.Input.LowerMIR
import MiriTests.Input.LoweringOracle

open Lean Miri Miri.Input

private def must (value : Except ε α) [ToString ε] : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

private def checkSharedScope : IO Unit := do
  let reference := fun id => Json.mkObj [("$lean_miri_shared_ref", toJson id)]
  let input := Json.mkObj [("shared_payloads", Json.mkObj [
    ("schema_version", toJson (2 : Nat)),
    ("nodes", Json.arr #[
      Json.mkObj [("kind", .str "Index"), ("status", .str "supported"), ("local", toJson (5 : Nat)),
        ("resulting_type", Json.mkObj [("type_id", toJson (0 : Nat))])],
      Json.arr #[reference (0 : Nat)],
      Json.mkObj [("status", .str "supported"), ("local", toJson (0 : Nat)),
        ("type", Json.mkObj [("type_id", toJson (0 : Nat))]), ("projection", reference (1 : Nat))]])])]
  let catalog ← must (Reader.Catalog.parse input)
  let decode := Reader.PlaceReader.place catalog 1 (reference (2 : Nat)) "place"
  let (id,state) ← must (decode.run (Reader.PlaceReader.initial catalog.nodes.size))
  let (same,state) ← must (decode.run state)
  unless id == same do throw (IO.userError "shared place lost identity")
  let _ ← must (Reader.PlaceReader.validatePlace state id 6)
  unless !(Reader.PlaceReader.validatePlace state same 5).isOk do
    throw (IO.userError "cached place validation leaked across body local scopes")

def main (args : List String) : IO Unit := do
  checkSharedScope
  let some path := args.head? | throw (IO.userError "usage: PlaceIDs <export.json>")
  let source ← IO.FS.readFile path
  -- Independent source-shaped oracle only; production keeps the wire DAG.
  let resolved ← must (SharedPayloads.resolveGraph (← must (Json.parse source)))
  let catalog ← must (Reader.Catalog.parse (← must (Json.parse source)))
  let decoded ← must (decodeRuntimeJson source)
  let context := LowerContext.ofDocument decoded.document
  let mut state := Reader.PlaceReader.initial catalog.nodes.size
  let mut places := 0
  let mut projections := 0
  for (raw,id) in catalog.nodes.toList.zipIdx do
    unless (raw.getObjVal? "local").isOk && (raw.getObjVal? "projection").isOk &&
        (raw.getObjVal? "type").isOk do continue
    let reference := Json.mkObj [("$lean_miri_shared_ref", toJson id)]
    let (place,next) ← must ((Reader.PlaceReader.place catalog decoded.document.types.size reference "place").run state)
    state := next
    unless place.index == id do throw (IO.userError "place wire ID changed")
    let node ← must (state.tables.places.lookup place.index)
    let ids ← must (state.tables.projectionLists.lookup node.projection.index)
    let values ← ids.mapM fun id => must (state.tables.projections.lookup id.index)
    let some raw := resolved.nodes[id]? | throw (IO.userError "place oracle absent")
    let expected ← must (MiriTests.Input.LoweringOracle.lowerCompilerPlace context (← must (context.decodeCompilerValue raw)))
    unless expected.localId == node.localId && expected.projection == values do
      throw (IO.userError "place semantics changed")
    let bound ← must (state.placeLocals.lookup place.index)
    let expectedBound := expected.projection.foldl (fun count projection => match projection with
      | .Index id => max count (id+1) | _ => count) (expected.localId+1)
    unless bound == expectedBound do throw (IO.userError "place local requirements changed")
    let _ ← must (Reader.PlaceReader.validatePlace state place bound)
    unless !(Reader.PlaceReader.validatePlace state place (bound-1)).isOk do
      throw (IO.userError "place accepted a smaller body scope")
    projections := projections + ids.size
    places := places + 1
  unless places > 0 && projections > 0 do throw (IO.userError "fixture lacks projected places")
  IO.println s!"place IDs: PASS ({places} places; {projections} projections; wire IDs and local scopes preserved)"
