import Miri.Input.CompilerConstantQueries
import Miri.Input.Decoder
import Miri.Input.LowerMIR

open Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected exporter input")
  let input ← must (decodeJson (← IO.FS.readFile path))
  for (body, id) in input.document.bodies.toList.zipIdx do
    let resolved ← must (NormalizationBody.resolve id input.document.bodies)
    check (resolved.sourcePath == body.sourcePath && resolved.definitionId == body.definitionId)
      "normalization body ID resolved to another definition"
  for invalid in #[input.document.bodies.size, 2^100] do
    check (!(NormalizationBody.resolve invalid input.document.bodies).isOk) "out of bounds body ID accepted"
  let program ← must (lowerProgram input.document)
  let prepared ← must (CompilerConstantQueries.prepare program)
  check (prepared.program.roots == program.roots && prepared.program.instances == program.instances &&
    prepared.program.promoted == program.promoted && prepared.program.bundle.spans == program.bundle.spans &&
    prepared.program.bundle.definitions == program.bundle.definitions &&
    prepared.program.bundle.typeConstants == program.bundle.typeConstants)
    "normalization preparation rewrote compiler pool identities"
  check (!prepared.evidence.isEmpty) "fixture contains no normalization query evidence"
  IO.println "normalization resolves body IDs without expansion and retains compiler pool identities"
