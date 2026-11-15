import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCallerLocation
import Miri.Input.SourceCompilerBodies
open Lean Miri Miri.Input Miri.Interpreter Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "missing caller-location evidence accepted")
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "usage: finite std source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let some source := initial.canonical.sourceMaterial | throw (IO.userError "typed source absent")
  let some abi := source.abi | throw (IO.userError "typed headers absent")
  let mut count := 0
  for node in initial.canonical.instances do
    if let .Item definition := node.instanceKind then
      let some raw := initial.canonical.definitions[definition]? | throw (IO.userError "raw definition absent")
      if let some header := abi.functions.find? (·.definition == raw) then
        let result ← checked (SourceCallerLocation.requiresCallerLocation initial node.id)
        unless result == header.attributes.trackCaller do throw (IO.userError "definition flag mismatch")
        let flipped := {source with abi := some {abi with functions := abi.functions.map fun entry =>
          if entry.definition == raw then {entry with attributes := {entry.attributes with
            trackCaller := !header.attributes.trackCaller}} else entry}}
        let changed ← checked (SourceCallerLocation.requiresCallerLocation
          {initial with canonical := {initial.canonical with sourceMaterial := some flipped}} node.id)
        unless changed == !result do throw (IO.userError "definition attribute was ignored")
        let missing := {source with abi := some {abi with functions := abi.functions.filter (·.definition != raw)}}
        rejects (SourceCallerLocation.requiresCallerLocation
          {initial with canonical := {initial.canonical with sourceMaterial := some missing}} node.id)
        count := count + 1
  unless count > 0 do throw (IO.userError "no genuine source caller flags checked")
  rejects (SourceCallerLocation.requiresCallerLocation initial initial.canonical.instances.size)
  let some root := initial.canonical.instances.find? (·.defPath == some "main")
    | throw (IO.userError "main instance absent")
  let (world,loaded) ← checked (SourceCompilerBodies.demandLoadedBody initial root.id)
  let scope ← checked (SourceCallerLocation.sourceScope world loaded.identity root.id loaded.body 0)
  unless scope.inlined.isNone do throw (IO.userError "fixture unexpectedly inlined")
  rejects (SourceCallerLocation.sourceScope world loaded.identity world.canonical.instances.size loaded.body 0)
  let some body := world.canonical.bodies[loaded.identity.index]? | throw (IO.userError "canonical body absent")
  let broken := {body with sourceScopes := body.sourceScopes.map fun scope =>
    {scope with spanId := world.canonical.spans.size}}
  let bodies := world.canonical.bodies.mapIdx fun index row => if index == loaded.identity.index then broken else row
  rejects (SourceCallerLocation.sourceScope {world with canonical := {world.canonical with bodies}}
    loaded.identity root.id loaded.body 0)
  IO.println s!"PASS {count} genuine definition flags, current body/scopes, missing callee/header/span controls"
