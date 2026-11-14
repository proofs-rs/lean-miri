import Miri.Input.Decoder
import Miri.Input.CompilerInstanceAbi

/-! Exercise the production material layout and ABI readers against fresh
rustc exports, then remove each demanded result from the immutable view. -/
open Miri.Input

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def inspect (path : String) : IO Unit := do
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let mut layouts := 0
  for node in document.types do
    let expected ← must ((runtime.lookup node.id).mapError toString)
    let (actual,_) ← must ((runtime.layoutInWorld node.id).run world.arena)
    check (actual == expected) s!"rustc layout result mismatch for type {node.id}"
    layouts := layouts + 1
  check (layouts > 0) "export has no material layouts"
  let some firstType := document.types[0]? | throw (IO.userError "material type absent")
  let missingRuntime := {runtime with source := {runtime.source with layouts := #[]}}
  check (!((missingRuntime.layoutInWorld firstType.id).run world.arena).isOk)
    "layout demand accepted a missing rustc result"

  let program ← must (lowerProgram document)
  let prepared ← must (CompilerInstanceAbi.prepare runtime program)
  check (!prepared.entries.isEmpty) "export has no exact rustc instance ABI"
  let some row := prepared.entries[0]? | throw (IO.userError "ABI row absent")
  let expected ← must (CallResolution.functionAbiId runtime (← must row.result))
  let (actual,_) ← must ((CompilerInstanceAbi.abiOfInstanceInWorld prepared row.callee row.extra).run world)
  check (actual == expected) "instance ABI differs from rustc result row"
  let missing := {prepared with entries := #[]}
  check (!((CompilerInstanceAbi.abiOfInstanceInWorld missing row.callee row.extra).run world).isOk)
    "instance ABI demand accepted a missing rustc result"
  let some item := document.instances.find? (fun node =>
      match node.instanceKind with | .Item _ => true | _ => false)
    | throw (IO.userError "export has no Item instance")
  let .Item definition := item.instanceKind | throw (IO.userError "Item selection invariant")
  check ((← must (CompilerInstance.Material.item document.instances definition item.genericArgs)) == item.id)
    "Item result differs from exact rustc instance row"
  check (!(CompilerInstance.Material.item #[] definition item.genericArgs).isOk)
    "Item lookup accepted a missing rustc instance result"
  IO.println s!"PASS {path}: {layouts} exact material layouts, ABI and Item missing-result boundaries"

def main (args : List String) : IO Unit := do
  let [first, second] := args | throw (IO.userError "expected two fresh rustc exports")
  inspect first
  inspect second
