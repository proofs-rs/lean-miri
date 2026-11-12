import MiriTests.Input.LegacyFixture
import Miri.Input.LowerMIR
import Miri.Input.Decoder

open Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let path := args.headD "examples/empty_function/input.json"
  let input ← must (decodeFixture (← IO.FS.readFile path))
  let program ← must (lowerProgram input.document)
  unless program.bodyCount == input.document.bodies.size &&
      program.bundle.spans == input.document.spans &&
      program.bundle.definitions == input.document.definitions &&
      program.bundle.typeConstants == input.document.typeConstants do
    throw (IO.userError "lowering changed compiler pool definitions or body IDs")
  for index in [:program.bodyCount] do
    let metadata ← must (program.bodyMetadata index)
    let expected ← match input.document.bodies[index]? with
      | some (.material _) => pure s!"$.bodies[{index}]"
      | some (.copyTemplate reference) =>
        unless reference.templateId < input.document.mirTemplates.size do
          throw (IO.userError "body path refers to an absent source template")
        pure s!"$.mir_templates[{reference.templateId}]"
      | none => throw (IO.userError "body path refers to an absent body seed")
    unless metadata.sourcePath == expected do
      throw (IO.userError s!"body diagnostic path does not resolve to its source definition: {index}")
  IO.println s!"source body paths and compiler pool IDs preserved for {program.bodyCount} definitions"
