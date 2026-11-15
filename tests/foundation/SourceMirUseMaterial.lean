import Miri.Frontend.FoundationSourceMaterial
open Lean Miri Miri.Input Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α := match r with
| .ok v => pure v | .error e => throw (IO.userError e)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "malformed MIR use source accepted")
private def replace (j : Json) (key : String) (v : Json) : Except String Json := do
  return Json.mkObj (((← j.getObj?).toArray.toList.filter (·.1 != key)) ++ [(key,v)])
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine catch use source")
  let d ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let source ← checked (typedSourceMaterial d)
  let some uses := source.mirUses | throw (IO.userError "MIR use source absent")
  let some mir := source.genericMir | throw (IO.userError "generic MIR source absent")
  let mut catchRows : Array DefinitionId := #[]
  for definition in d.definitions do
    if (← checked (definition.getObjValAs? String "path")) == "std::panic::catch_unwind" then
      catchRows := catchRows.push ⟨← checked (definition.getObjValAs? Nat "crate_index"),← checked (definition.getObjValAs? Nat "index")⟩
  unless catchRows.size == 1 do throw (IO.userError "genuine catch declaration absent/ambiguous")
  let mut found := 0
  let mut events := 0
  for row in uses.declarations do
    if let some body := row.body then
      events := events+body.events.size
      let sourceBodies := mir.bodies.filter (·.definition == row.definition)
      for rawBody in sourceBodies do
        unless catchRows.contains row.definition do continue
        let directCalls := rawBody.blocks.any fun block => match block.terminator.kind with
          | .call _ _ destination _ _ _ _ => destination.localId == 0 && destination.projection.isEmpty
          | _ => false
        if directCalls then
          unless body.events.any (fun event => match event.kind with
            | .place place (.mutating .call) => place.localId == 0 && place.firstProjection.isNone
            | _ => false) do throw (IO.userError "full source direct return Call missing from use stream")
          found := found+1
  unless found > 0 && events > 0 do throw (IO.userError "actual full MIR/use correspondence absent")
  let raw ← checked (d.source.getObjVal? "mir_use_source")
  let rows ← checked (raw.getObjValAs? (Array Json) "declarations")
  let mut controls := 0
  for row in rows do
    let body ← checked (row.getObjVal? "body")
    if body != .null then
      for (key,value) in #[("event_count",toJson (events+1)),("source_definition",toJson d.definitions.size)] do
        let changed ← checked (replace row "body" (← checked (replace body key value)))
        let changed ← checked (replace raw "declarations" (toJson #[changed]))
        rejects (SourceMirUsesParser.material {d with source := ← checked (replace d.source "mir_use_source" changed)})
      controls := controls+1
  unless controls > 0 do throw (IO.userError "no MIR use controls")
  IO.println s!"PASS {uses.declarations.size} generic declarations/{events} use events; raw full-MIR Call correspondence and count/owner controls"
