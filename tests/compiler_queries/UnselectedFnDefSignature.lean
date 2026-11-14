import Miri.Input.Decoder
import Miri.Input.CompilerFunctionFacts

/-! A trait FnDef declaration has a rustc normalized signature before an
implementation is selected. Removing that signature must reject the demand. -/
open Miri.Input

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a fresh trait-call export")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let program ← must (lowerProgram document)
  let prepared ← must (CompilerFunctionFacts.prepare runtime program)
  let some row := document.queries.functionFacts.types.find? (fun entry =>
    entry.instanceId.isNone && (document.types[entry.typeId]?).any (fun node =>
      node.shapeKind == .functionDefinition))
    | throw (IO.userError "no unselected trait FnDef signature was exported")
  let (actual,_) ← must ((CompilerFunctionFacts.signatureInWorld prepared row.typeId).run world)
  unless actual == (row.signature.inputs.size, row.signature.abi) do
    throw (IO.userError "trait FnDef signature differs from rustc result")
  let missing := {prepared with functions := prepared.functions.filter (·.ty != row.typeId)}
  unless !((CompilerFunctionFacts.signatureInWorld missing row.typeId).run world).isOk do
    throw (IO.userError "missing trait FnDef rustc signature was accepted")
  IO.println s!"PASS unselected FnDef rustc signature: type {row.typeId}"
