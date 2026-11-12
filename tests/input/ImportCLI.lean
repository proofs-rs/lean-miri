import MiriTests.Input.LegacyFixture
import Miri.Input

open Miri.Input

def main (args : List String) : IO UInt32 := do
  match args with
  | path :: _ =>
    let result ← decodeFixtureFile path
    match result with
    | .error error =>
      IO.eprintln error
      return 1
    | .ok decoded =>
      IO.println s!"imported schema-4 MIR: bodies={decoded.document.bodies.size}, instances={decoded.document.instances.size}, types={decoded.document.types.size}, allocations={decoded.document.allocations.size}"
      return 0
  | _ =>
    IO.eprintln "usage: ImportCLI <export.json>"
    return 2
