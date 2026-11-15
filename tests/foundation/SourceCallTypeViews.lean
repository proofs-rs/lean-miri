import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
import Miri.Input.CompilerExecutionCallLeaves
open Lean Miri Miri.Input Miri.Interpreter Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "unavailable call type evidence accepted")
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected actual std source")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let mut world := initial
  for node in initial.canonical.instances do
    let (updated,_) ← checked (SourceCompilerBodies.demandLoadedBody world node.id)
    world := updated
  let mut tuples := 0
  let mut closures := 0
  let mut grown := 0
  for node in world.canonical.types do
    let count ← checked (CompilerExecutionCallLeaves.closureUpvarCountSource world node.id)
    match node.shape with
    | .tuple elements =>
      tuples := tuples+1
      unless count.isNone && (← checked (CompilerExecutionCallLeaves.tupleFieldsSource world node.id)) == elements do
        throw (IO.userError "canonical tuple children changed during call spreading")
    | .closure _ _ expected =>
      closures := closures+1
      if node.id >= initial.canonical.types.size then grown := grown+1
      unless count == some expected do throw (IO.userError "canonical closure upvar count changed")
      rejects (CompilerExecutionCallLeaves.tupleFieldsSource world node.id)
    | _ =>
      unless count.isNone do throw (IO.userError "nonclosure acquired capture count")
      rejects (CompilerExecutionCallLeaves.tupleFieldsSource world node.id)
  unless tuples > 0 && closures > 0 && grown > 0 do throw (IO.userError "genuine demanded tuple/closure pool growth absent")
  rejects (CompilerExecutionCallLeaves.tupleFieldsSource world world.canonical.types.size)
  rejects (CompilerExecutionCallLeaves.closureUpvarCountSource world world.canonical.types.size)
  IO.println "call tuple/closure queries use grown canonical World IDs; exact children/counts preserved and missing/non-tuple cases reject"
