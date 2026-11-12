import MiriTests.Input.LegacyFixture
import Miri.Input.Decoder

open Miri.Input

def main (args : List String) : IO UInt32 := do
  let path ← match args with
    | value :: _ => pure value
    | [] => throw (IO.userError "usage: NoopTests <rooted-coverage-export.json>")
  let .ok result := decodeFixture (← IO.FS.readFile path)
    | throw (IO.userError "rooted coverage export rejected")
  let mut covered := false
  for index in [:result.document.bodies.size] do
    let .ok body := SourceMir.resolveBody result.document index
      | throw (IO.userError "rooted coverage body resolution failed")
    covered := covered || body.mir.basicBlocks.any (fun block =>
      block.statements.any fun statement => match statement.kind with | .Coverage _ => true | _ => false)
  unless covered do
    throw (IO.userError "Coverage did not decode directly to MIR")
  IO.println "rooted Coverage decoded directly to MIR"
  return 0
