import Miri.Input.LowerMIR
import Miri.Input.Decoder

open Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let path := args.headD "examples/empty_function/input.json"
  let input ← must (decodeJson (← IO.FS.readFile path))
  let program ← must (lowerProgram input.document)
  unless program.bundle.bodies.size == input.document.bodies.size &&
      program.bundle.spans == input.document.spans &&
      program.bundle.definitions == input.document.definitions &&
      program.bundle.typeConstants == input.document.typeConstants do
    throw (IO.userError "lowering changed compiler pool definitions or body IDs")
  for (lowered, index) in program.bundle.bodies.toList.zipIdx do
    unless lowered.input.sourcePath == s!"$.bodies[{index}]" do
      throw (IO.userError s!"body diagnostic path does not resolve to its source definition: {index}")
  IO.println s!"source body paths and compiler pool IDs preserved for {program.bundle.bodies.size} definitions"
