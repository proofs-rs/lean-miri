import Miri.Frontend.FoundationNamedTypes
import Miri.Input.Decoder
open Lean Miri Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def failure {α : Type} (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "ambiguous/missing alias source accepted")
def main (paths : List String) : IO Unit := do
  let [finitePath,compilerPath] := paths | throw (IO.userError "expected finite/compiler named type inputs")
  let document ← checked (Json.parse (← IO.FS.readFile finitePath) >>= decode)
  let (physical,names) ← checked (startupNamedTypes (PhysicalTypeRegistry.start document))
  let ordinary ← checked (Input.decodeJson (← IO.FS.readFile compilerPath))
  let some compilerNames := ordinary.document.queries.namedTypes | throw (IO.userError "compiler named types absent")
  let target ← checked (runtimeTargetOfTarget document.target)
  for (name,id) in names do
    let some (_,actualId) := compilerNames.find? (·.1 == name) | throw (IO.userError "compiler startup key absent")
    let some actual := ordinary.document.types[actualId]? | throw (IO.userError "compiler named type absent")
    let some layout := ordinary.document.layouts[actual.layoutId]? | throw (IO.userError "compiler named layout absent")
    let computed ← checked (physical.runtimeLayout id)
    let compilerLayout ← checked ((Input.RuntimeMetadata.layout target layout).mapError toString)
    unless computed.layout == compilerLayout do throw (IO.userError "source alias/pointer physical layout differs from compiler")
  let source ← checked (document.source.getObjVal? "named_type_source")
  for key in #["roots","modules","aliases"] do
    let rows ← checked (source.getObjValAs? (Array Json) key)
    let some first := rows[0]? | throw (IO.userError "source declaration table empty")
    -- Duplicating the complete table preserves even non-first alias matches.
    let duplicate := source.setObjVal! key (toJson (rows ++ rows))
    failure (namedAliasSource { document with source := document.source.setObjVal! "named_type_source" duplicate } #["core","ffi","c_ulong"])
    let missing := source.setObjVal! key (toJson (#[] : Array Json))
    failure (namedAliasSource { document with source := document.source.setObjVal! "named_type_source" missing } #["core","ffi","c_ulong"])
    let _ := first
  let aliases ← checked (source.getObjValAs? (Array Json) "aliases")
  for (key,value) in #[("rhs",Json.null),("generic_parameter_count",toJson (1 : Nat))] do
    let aliases := aliases.map fun alias =>
      if (alias.getObjValAs? String "name").toOption == some "c_ulong" then alias.setObjVal! key value else alias
    let changed := source.setObjVal! "aliases" (toJson aliases)
    failure (namedAliasSource { document with source := document.source.setObjVal! "named_type_source" changed } #["core","ffi","c_ulong"])
  failure (namedAliasSource document #["libc","off_t"])
  IO.println "startup named types: source C-ulong alias and mutable i32 pointer full layouts match compiler; missing/ambiguous/symbolic source and uncaptured OS name reject"
