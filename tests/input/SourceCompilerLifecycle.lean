import Miri.Frontend.FoundationEntrySeed
import Miri.Input.CompilerLifecycle
import Miri.Input.SourceCompilerBodies
open Lean Miri Miri.Input Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "invalid lifecycle metadata accepted")

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine custom main source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  unless initial.canonical.bodies.isEmpty do throw (IO.userError "source body eagerly installed")
  let some node := initial.canonical.instances.find? (·.defPath == some "main")
    | throw (IO.userError "main identity absent")
  let (world,loaded) ← checked (SourceCompilerBodies.demandLoadedBody initial node.id)
  let span ← checked (CompilerLifecycle.sourcePreambleSpan world loaded)
  let some body := world.canonical.bodies[loaded.identity.index]?
    | throw (IO.userError "installed body absent")
  unless span.id == body.preambleDefSpanId do throw (IO.userError "current preamble identity changed")
  rejects (CompilerLifecycle.sourcePreambleSpan initial loaded)
  rejects (CompilerLifecycle.sourcePreambleSpan
    {world with canonical := {world.canonical with spans := #[]}} loaded)
  let wrong := {loaded with identity := .ofCanonicalIndex world.canonical.bodies.size}
  rejects (CompilerLifecycle.sourcePreambleSpan world wrong)
  let body := {body with instanceId := world.canonical.instances.size}
  let broken := {world with canonical := {world.canonical with
    bodies := world.canonical.bodies.set! loaded.identity.index body}}
  rejects (CompilerLifecycle.sourcePreambleSpan broken loaded)
  IO.println "live lifecycle: demanded body/span identity preserved; stale World/missing span/wrong body owner reject"
