import Miri.Frontend.FoundationSourceTypes
import Miri.Input.SourceTypeQueries
open Lean Miri Miri.Input.SourceTypes
private def expect (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def check (b : Bool) (m : String) : IO Unit := unless b do throw (IO.userError m)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "invalid/unsupported source type accepted")
def main (paths : List String) : IO Unit := do
  for path in paths do
    let raw ← expect (Json.parse (← IO.FS.readFile path))
    let source ← expect (Frontend.Foundation.SourceTypesParser.material raw)
    let original ← expect (raw.getObjValAs? (Array Json) "types")
    check (source.types.size == original.size) "typed row coverage changed"
    source.validate |> expect
    if let some id := source.types.findIdx? (fun t => match t with | .parameter .. => true | _ => false) then
      let some (.parameter parameter _) := source.types[id]? | throw (IO.userError "parameter missing")
      let bindings := (List.range (parameter+1)).toArray.map fun i => if i == parameter then some (Concrete.tuple #[]) else none
      let actual ← expect (instantiate source bindings #[] id)
      check (match actual with | .tuple xs => xs.isEmpty | _ => false) "typed generic substitution failed"
      rejects (instantiate source #[] #[] id)
    let mut types := source.types
    types := types.push (.unsupported "future semantic type")
    let deferred := {source with types}
    let _ ← expect deferred.validate
    rejects (instantiate deferred #[] #[] source.types.size)
    let malformed := {source with types := source.types.push (.tuple #[source.types.size+1])}
    rejects malformed.validate
    let brokenRow := Json.mkObj [("type_id",toJson source.types.size),("shape",Json.mkObj [("kind",toJson "tuple"),("elements",toJson #[source.types.size+1])])]
    rejects (Frontend.Foundation.SourceTypesParser.material (raw.setObjVal! "types" (toJson (original.push brokenRow))))
    IO.println s!"PASS {source.types.size} typed source rows retained, substitution and deferred/invalid controls"
