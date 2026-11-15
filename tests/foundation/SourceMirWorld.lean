import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
open Lean Miri Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported body demand accepted")

def main (paths : List String) : IO Unit := do
  for path in paths do
    let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
    let initial ← checked (compilerEntrySeed document)
    unless initial.canonical.bodies.isEmpty do throw (IO.userError "source seed eagerly installed MIR")
    let some main := initial.canonical.instances.find? (·.defPath == some "main")
      | throw (IO.userError "main identity absent")
    rejects (Input.SourceCompilerBodies.loadedBodyOfInstance initial main.id)
    let (world,_) ← checked (Input.SourceCompilerBodies.demandLoadedBody initial main.id)
    unless world.canonical.bodies.size == 1 && initial.canonical.bodies.isEmpty do
      throw (IO.userError "demanded body installation did not persist precisely")
    let (again,_) ← checked (Input.SourceCompilerBodies.demandLoadedBody world main.id)
    unless again.canonical.bodies.size == 1 && again.canonical.spans == world.canonical.spans do
      throw (IO.userError "repeated body demand grew canonical pools")
    let some source := initial.canonical.sourceMaterial | throw (IO.userError "source absent")
    rejects (Input.SourceCompilerBodies.demandLoadedBody
      {initial with canonical := {initial.canonical with sourceMaterial := some {source with genericMir := none}}} main.id)
    let some mir := source.genericMir | throw (IO.userError "typed MIR absent")
    let unsupported := {mir with bodies := mir.bodies.map fun body =>
      {body with blocks := body.blocks.map fun block =>
        {block with terminator := {block.terminator with kind := .unsupported "test-unknown"}}}}
    rejects (Input.SourceCompilerBodies.demandLoadedBody
      {initial with canonical := {initial.canonical with sourceMaterial := some {source with genericMir := some unsupported}}} main.id)
    let some start := world.canonical.instances.find? (·.defPath == some "start")
      | throw (IO.userError "start identity absent")
    let (both,_) ← checked (Input.SourceCompilerBodies.demandLoadedBody world start.id)
    unless both.canonical.bodies.size == 2 do throw (IO.userError "generic start body not installed")
    IO.println s!"typed World MIR {path}: main/start demand installs2 bodies; repeated demand stable; absent/unsupported reject"
