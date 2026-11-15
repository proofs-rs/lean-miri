import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
import Miri.Input.SourceCompilerRuntime
import Miri.Input.CompilerStorage
open Lean Miri Miri.Input Miri.Interpreter Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine ordinary std source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let baseline ← checked (RuntimeMetadata.ofDocument initial.canonical |>.mapError toString)
  let some entry := initial.canonical.queries.main.entries[0]? | throw (IO.userError "entry absent")
  let some start := entry.signature.startResolution | throw (IO.userError "start resolution absent")
  let (world,loaded) ← checked (SourceCompilerBodies.demandLoadedBody initial start.instanceId)
  let some block := loaded.body.basicBlocks[0]? | throw (IO.userError "start block absent")
  let some statement := block.statements[0]? | throw (IO.userError "first statement absent")
  let .StorageLive localId := statement.kind | throw (IO.userError "expected genuine first StorageLive")
  let some ty := loaded.body.locals[localId]? | throw (IO.userError "scheduled local type absent")
  match baseline.lookup ty with
  | .ok _ => throw (IO.userError "control type already present before demand")
  | .error _ => pure ()
  let access : SourceCompilerWorld.Access SourceCompilerWorld.World := ⟨some,fun _ next => next⟩
  match SourceCompilerRuntime.current baseline.target access world with
  | .error error _ => throw (IO.userError (reprStr error))
  | .ok runtime after =>
    unless runtime.source.types.size == world.canonical.types.size && after.canonical.types.size == world.canonical.types.size do
      throw (IO.userError "runtime view lost current types or mutated World")
    let node ← checked (runtime.node ty |>.mapError toString)
    let .reference .. := node.shape | throw (IO.userError "expected actual reference local")
    unless (← checked (CompilerStorage.veryTriviallySized runtime ty |>.mapError reprStr)) do
      throw (IO.userError "live reference trivially-sized classification changed")
    let _ ← checked (runtime.lookup ty |>.mapError toString)
  let unavailable : SourceCompilerWorld.Access Unit := ⟨fun _ => none,fun _ _ => ()⟩
  match SourceCompilerRuntime.current baseline.target unavailable () with
  | .error (.unsupported _) _ => pure ()
  | _ => throw (IO.userError "missing World silently fell back to frozen metadata")
  IO.println "live runtime: genuine first std StorageLive type absent in prepared view, present/sized in current World; absent World rejects"
