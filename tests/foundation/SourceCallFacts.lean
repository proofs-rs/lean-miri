import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCallFacts
open Lean Miri Miri.Input Miri.Interpreter Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "missing foreign-call evidence accepted")
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "usage: finite std source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let some source := initial.canonical.sourceMaterial | throw (IO.userError "source absent")
  let some abi := source.abi | throw (IO.userError "headers absent")
  let mut count := 0
  for node in initial.canonical.instances do
    let definition := node.instanceKind.defId
    let some raw := initial.canonical.definitions[definition]? | throw (IO.userError "raw definition absent")
    if let some header := abi.functions.find? (·.definition == raw) then
      let result ← checked (SourceCallFacts.isForeignItem initial node.id)
      unless result == header.attributes.foreignItem do throw (IO.userError "foreign declaration flag differs")
      let changed := {source with abi := some {abi with functions := abi.functions.map fun entry =>
        if entry.definition == raw then {entry with attributes := {entry.attributes with
          foreignItem := !header.attributes.foreignItem}} else entry}}
      let changedWorld := {initial with canonical := {initial.canonical with sourceMaterial := some changed}}
      unless (← checked (SourceCallFacts.isForeignItem changedWorld node.id)) == !result do
        throw (IO.userError "foreign classification ignored the definition attribute")
      rejects (SourceCallFacts.symbolName changedWorld node.id)
      let missing := {source with abi := some {abi with functions := abi.functions.filter (·.definition != raw)}}
      rejects (SourceCallFacts.isForeignItem {initial with canonical := {initial.canonical with sourceMaterial := some missing}} node.id)
      let ambiguous := {source with abi := some {abi with functions := abi.functions.push header}}
      rejects (SourceCallFacts.isForeignItem {initial with canonical := {initial.canonical with sourceMaterial := some ambiguous}} node.id)
      -- ClosureOnce::def_id is call_once, not the closure definition. Copying
      -- a synthetic kind here checks selection only, not shim executability.
      let shim := {node with instanceKind := .Shim (.ClosureOnce definition initial.canonical.definitions.size false)}
      let instances := changedWorld.canonical.instances.map fun entry => if entry.id == node.id then shim else entry
      let shimWorld := {changedWorld with canonical := {changedWorld.canonical with instances}}
      unless (← checked (SourceCallFacts.isForeignItem shimWorld node.id)) == !result do
        throw (IO.userError "ClosureOnce foreign query selected closure instead of call_once")
      count := count+1
  unless count > 0 do throw (IO.userError "no genuine declaration flags tested")
  rejects (SourceCallFacts.isForeignItem initial initial.canonical.instances.size)
  IO.println s!"PASS {count} genuine foreign declaration flags, attribute/shim selection, missing/ambiguous keys and unsupported symbol naming"
