import Miri.Input.Decoder
import Miri.Input.ConcreteCovariance
import Miri.Input.ConcreteCastQueries
import Miri.Input.SourceAbiRuntime

open Miri Miri.Input Miri.MIR

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error reason => throw (IO.userError reason)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh source-material export")
  let decoded ← decodeFile path
  let document ← match decoded with
    | .ok input => pure input.document
    | .error reason => throw (IO.userError reason)
  let runtime ← must (RuntimeMetadata.ofDocument document |>.mapError toString)
  let some base := document.types.find? fun node => match node.shape with
      | .uint (.known .u32) => true | _ => false
    | throw (IO.userError "control requires an exported u32 type")
  let mut types := document.types
  let erased := types.size
  types := types.push {id := erased, display := "erased reference control", shape := .reference base.id .Not .Erased}
  let static := types.size
  types := types.push {id := static, display := "static reference control", shape := .reference base.id .Not .Static}
  let mutable := types.size
  types := types.push {id := mutable, display := "mutable reference control", shape := .reference base.id .Mut .Erased}
  let escaping := types.size
  types := types.push {id := escaping, display := "escaping reference control", shape := .reference base.id .Not (.Bound (.Bound 0) 0 .Anon)}
  let function := types.size
  let signature : FunctionSignature := {
    inputs := #[escaping], output := base.id, safety := .Safe, abi := .Rust, cVariadic := false }
  types := types.push {
    id := function, display := "higher-ranked function control"
    shape := .functionPointer signature #[.Region .Anon]}
  let unsafeFunction := types.size
  types := types.push {
    id := unsafeFunction, display := "unsafe function control"
    shape := .functionPointer {signature with safety := .Unsafe} #[.Region .Anon]}
  let controls : RuntimeMetadata := {source := {document with types}, target := runtime.target}
  check ((← must (ConcreteCovariance.relation controls erased static)))
    "region-ignoring relation rejected shared references"
  check (!(← must (ConcreteCovariance.relation controls erased mutable)))
    "reference mutability mismatch accepted"
  check (!(← must (ConcreteCovariance.relation controls function unsafeFunction)))
    "function safety mismatch accepted"
  check (!(← must (ConcreteCastQueries.noBoundVars controls #[.Type escaping])))
    "escaping bound lifetime accepted"
  check ((← must (ConcreteCastQueries.noBoundVars controls #[.Type function])))
    "function's own higher-ranked lifetime treated as escaping"
  for target in document.sourceCastTargets do
    let input := match target with | .functionPointer input _ | .closureOnce input _ => input
    let source ← must (runtime.node input |>.mapError toString)
    let args := match source.shape with
      | .functionDefinition _ args _ _ | .closure _ args _ => args
      | _ => #[]
    check ((← must (ConcreteCastQueries.noBoundVars runtime args)))
      "actual source cast has escaping bound variables"
  IO.println s!"source query controls: lifetime binders, reference mutability, function safety; actual casts={document.sourceCastTargets.size}; synthetic controls are separate from compiler comparisons"
