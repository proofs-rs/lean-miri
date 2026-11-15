import Miri.Frontend.FoundationSourceMaterial
open Lean Miri Miri.Input Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α := match r with
| .ok v => pure v | .error e => throw (IO.userError e)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "contradictory defining crate source accepted")
private def replace (j : Json) (key : String) (value : Json) : Except String Json := do
  return Json.mkObj (((← j.getObj?).toArray.toList.filter (·.1 != key)) ++ [(key,value)])
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected matched defining source")
  let d ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let full ← checked (typedSourceMaterial d)
  let some abi := full.abi | throw (IO.userError "typed ABI source absent")
  let compilation ← checked (d.source.getObjVal? "compilation")
  let incremental ← checked (compilation.getObjValAs? Bool "incremental")
  unless abi.callerIncremental == some incremental do throw (IO.userError "caller incremental source lost")
  let some typed ← checked (SourceMirUsesParser.material d) | throw (IO.userError "MIR use source absent")
  unless typed.declarations.any (fun row => row.compilation.any (·.freezeLangItemPresent.isSome)) do
    throw (IO.userError "actual defining Freeze source capability absent")
  unless typed.declarations.all (·.alwaysConst.isSome) do throw (IO.userError "declaration constness source absent")
  let source ← checked (d.source.getObjVal? "mir_use_source")
  let rows ← checked (source.getObjValAs? (Array Json) "declarations")
  let mut controls := 0
  for first in rows do
    let id ← checked (first.getObjValAs? Nat "definition")
    let some declaration := d.definitions[id]? | throw (IO.userError "owner absent")
    let crateId ← checked (declaration.getObjValAs? Nat "crate_index")
    let firstCompilation ← checked (first.getObjVal? "compilation")
    if firstCompilation == .null then continue
    for second in rows do
      let secondId ← checked (second.getObjValAs? Nat "definition")
      if secondId == id then continue
      let some secondDefinition := d.definitions[secondId]? | throw (IO.userError "second owner absent")
      unless (← checked (secondDefinition.getObjValAs? Nat "crate_index")) == crateId do continue
      let incremental ← checked (firstCompilation.getObjValAs? Bool "incremental")
      for altered in #[Json.null, ← checked (replace firstCompilation "incremental" (toJson (!incremental))),
          ← checked (replace firstCompilation "freeze_lang_item_present" .null)] do
        let changed ← checked (replace second "compilation" altered)
        let changed ← checked (replace source "declarations" (toJson #[first,changed]))
        rejects (SourceMirUsesParser.material {d with source := ← checked (replace d.source "mir_use_source" changed)})
      controls := controls+1
  unless controls > 0 do throw (IO.userError "same defining crate source pair absent")
  IO.println s!"PASS {typed.declarations.size} matched defining options/Freeze/declaration-constness rows; contradictory known/unknown same-crate facts reject"
