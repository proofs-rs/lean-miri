import Miri.Frontend.FoundationInput
import Miri.Input.SourceCompilerAllocations
open Lean Miri Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected genuine static initializer source")
  let decoded ← checked (decodeRunnerInputProfiled (← IO.FS.readFile path) {})
  let some world := decoded.initialWorld | throw (IO.userError "normal source World absent")
  let some material := world.canonical.sourceMaterial | throw (IO.userError "typed source missing")
  let some allocations := material.allocations | throw (IO.userError "allocation source missing")
  let some image := allocations.images[0]? | throw (IO.userError "genuine static graph root absent")
  let .static declaration := image.payload | throw (IO.userError "source Static became a memory answer")
  unless declaration.path == "VALUE" && !declaration.mutable && !declaration.threadLocal &&
      !declaration.foreignItem && world.canonical.allocations.isEmpty do
    throw (IO.userError "static source identity/attributes changed or eager image fabricated")
  let body ← checked declaration.initializer
  let some block := body.blocks[0]? | throw (IO.userError "static initializer source body absent")
  let some statement := block.statements[0]? | throw (IO.userError "static initializer source expression absent")
  match statement with
  | .assign place (.use (.constant constant) _) =>
    unless place.localId == 0 && place.projection.isEmpty && constant.type == declaration.type do
      throw (IO.userError "static initializer type/place source mismatch")
    match constant.value with
    | .scalar bits size => unless bits == 37 && size == 1 do throw (IO.userError "static literal source differs from Rust fixture")
    | _ => throw (IO.userError "static literal source not retained")
  | _ => throw (IO.userError "static initializer expression source not retained")
  match Input.SourceCompilerAllocations.demand world image.id with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "missing static initializer query synthesized backing bytes")
  IO.println "normal static source: raw global identity/declaration and initializer MIR retained; missing evaluation capability rejects without fabricated memory"
