import Miri.Frontend.FoundationInput
open Lean Miri Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
/-- Exercise the normal decoder result type and normal fixed input lowerer,
without running a dedicated source evaluator or assuming process completion. -/
def main (paths : List String) : IO Unit := do
  let [sourcePath,ordinaryPath] := paths | throw (IO.userError "expected source/custom and ordinary compiler inputs")
  let source ← IO.FS.readFile sourcePath
  let decoded ← checked (decodeRunnerInputProfiled source {})
  let program ← checked (Input.lowerProgram decoded.document)
  unless program.input.bodyRoots.isEmpty && program.input.bodies.isEmpty &&
      program.input.queries.main.entries.size == 1 &&
      program.input.instances.all (fun node => node.kind == .identityOnly && node.bodyId.isNone) do
    throw (IO.userError "header seed fabricated executable source bodies")
  let some world := decoded.initialWorld | throw (IO.userError "derived startup World discarded")
  unless world.derivedInstanceAbis.size == 2 && world.canonical.sourceMaterial.isSome do
    throw (IO.userError "typed material or derived header ABI memo discarded")
  let ordinary ← IO.FS.readFile ordinaryPath
  let existing ← checked (Input.decodeJson ordinary)
  let routed ← checked (decodeRunnerInputProfiled ordinary {})
  unless routed.document.bodies.size == existing.document.bodies.size &&
      routed.document.instances.size == existing.document.instances.size do
    throw (IO.userError "ordinary successful decoder path changed")
  let invalid := "{\"schema\":\"unknown\",\"schema_version\":1}"
  match Input.decodeJson invalid, decodeRunnerInputProfiled invalid {} with
  | .error expected, .error actual =>
    unless actual == expected do throw (IO.userError "ordinary invalid-input diagnostic changed")
  | _, _ => throw (IO.userError "unknown input unexpectedly accepted")
  IO.println "normal input dispatch: typed header-only World reaches normal lowerer without fabricated MIR; derived ABI memo and ordinary decode paths preserved"
