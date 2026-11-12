import Miri.Input.CtfeMirSourceCodec
open Lean Miri.Input Miri.Interpreter.CompileTime
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def outputTrace (state : ScalarFrame.State) : IO Unit := do
  for ((block,statement,counter),index) in state.trace.zipIdx do
    IO.println s!"step\t{index}\t{block}\t{statement}\t{counter}"
def main (args : List String) : IO Unit := do
  let [path,input,tiny,deny,count] := args | throw (IO.userError "source input tiny deny span-count")
  let source ← must (CtfeMirSourceCodec.read (← must (Json.parse (← IO.FS.readFile path))))
  let some spanCount := count.toNat? | throw (IO.userError "invalid span count")
  must (CtfeMirSource.validateReferences spanCount (· == source.definition) source)
  must (CtfeMirSource.validateCatalogue spanCount (· == source.definition) #[source])
  unless !(CtfeMirSource.validateCatalogue spanCount (· == source.definition) #[source,source]).isOk do
    throw (IO.userError "duplicate canonical CTFE source catalogue key was accepted")
  let _ ← must (CtfeMirSource.lookup #[source] source.definition source.promoted)
  unless !(CtfeMirSource.lookup #[] source.definition source.promoted).isOk &&
      !(CtfeMirSource.lookup #[source,source] source.definition source.promoted).isOk do
    throw (IO.userError "missing/duplicate physical CTFE source was accepted")
  let some input := input.toNat? | throw (IO.userError "invalid scalar input")
  let initial ← must (ScalarFrame.initializeState source.program #[.uint 32 input])
  match ScalarFrame.run source.program ⟨64,tiny == "1",deny == "1"⟩ 1000000 initial with
  | .returned (.uint _ value) state =>
    outputTrace state
    IO.println s!"result\t{state.steps}\t{state.counters}\t{value}"
  | .failed error state =>
    outputTrace state
    IO.println s!"error\t{state.steps}\t{state.counters}\t{error}"
  | _ => throw (IO.userError "unexpected scalar-frame outcome")
