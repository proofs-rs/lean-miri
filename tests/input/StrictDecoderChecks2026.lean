import Miri.Input.Decoder

open Lean Miri.Input Miri.Input.DecoderValues

private def must (outcome : Except String α) : IO α := do
  match outcome with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def set (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (Json.mkObj ((key, child) :: fields.toList.filter (fun item => item.1 != key)))

private def reject (input : Json) (label : String) : IO Unit := do
  for outcome in #[decodeJson input.compress |>.map (fun _ => ()),
      decodeRuntimeJson input.compress |>.map (fun _ => ()),
      decodeJsonReference input.compress |>.map (fun _ => ()),
      decodeRuntimeJsonReference input.compress |>.map (fun _ => ())] do
    if outcome.isOk then throw (IO.userError s!"{label}: failed input was accepted")

private def rejectSelector (outcome : Except String α) (label : String) : IO Unit :=
  if outcome.isOk then throw (IO.userError s!"{label}: unknown enum was accepted") else pure ()

def main : IO Unit := do
  let fixture ← must (Json.parse (← IO.FS.readFile "tests/input/fixtures/strict-unit.json"))
  let full ← must (decodeJson fixture.compress)
  let runtime ← must (decodeRuntimeJson fixture.compress)
  unless full.executionInput.document.raw == runtime.executionInput.document.raw do
    throw (IO.userError "successful full/runtime input differs")
  let unusedCatalog := Json.mkObj [("schema_version", toJson (2 : Nat)),
    ("nodes", .arr #[Json.mkObj [("$lean_miri_shared_ref", toJson (99 : Nat))]])]
  reject (← must (set fixture "shared_payloads" unusedCatalog)) "unreachable invalid transport reference"
  -- Semantic validation stops before decoding later compiler evidence. All
  -- import modes must report the first scope failure, without collecting it.
  let invalidScope := Json.mkObj [("kind", .str "future_scope"),
    ("semantics", .str "structural_export_closure_only"), ("roots", .arr #[])]
  let earlyFailure ← must (set fixture "selected_scope" invalidScope)
  let earlyFailure ← must (set earlyFailure "compiler_predicate_queries" (.arr #[.null]))
  for outcome in #[decodeJson earlyFailure.compress |>.map (fun _ => ()),
      decodeRuntimeJson earlyFailure.compress |>.map (fun _ => ()),
      decodeJsonReference earlyFailure.compress |>.map (fun _ => ()),
      decodeRuntimeJsonReference earlyFailure.compress |>.map (fun _ => ())] do
    match outcome with
    | .error message =>
      unless message == "$.selected_scope.kind: unrecognized selected-scope kind `future_scope`" do
        throw (IO.userError s!"semantic validation did not stop immediately: {message}")
    | .ok _ => throw (IO.userError "invalid selected scope was accepted")
  rejectSelector (statementVariant "FutureStatement") "statement"
  rejectSelector (terminatorVariant "FutureTerminator") "terminator"
  rejectSelector (rvalueVariant "FutureRvalue") "rvalue"
  rejectSelector (operandVariant "FutureOperand") "operand"
  rejectSelector (projectionVariant "FutureProjection") "projection"
  rejectSelector (typeShapeKind "future_type") "type shape"
  for kind in #["coroutine_witness", "parameter", "bound_type", "placeholder_type", "inference_type", "error_type"] do
    rejectSelector (typeShapeKind kind) s!"unresolved type shape {kind}"
  for kind in #["inference_variable", "error"] do
    let region := Json.mkObj [("kind", .str kind)]
    rejectSelector (decodeValue region "$region" .any (some .regionKind)) s!"unresolved region {kind}"
  for kind in #["parameter", "bound", "placeholder", "inference", "error"] do
    let constant := Json.mkObj [("kind", .str kind)]
    let argument := Json.mkObj [("kind", .str "const"), ("value", constant)]
    rejectSelector (decodeValue argument "$generic_argument") s!"unresolved constant {kind}"
  rejectSelector (integerTypeTag "u256") "integer kind"
  rejectSelector (layoutVariantsKind "future_layout") "layout variant"
  rejectSelector (backendReprKind "future_backend") "backend representation"
  rejectSelector (canonicalAbiKind "future_abi") "ABI"
  rejectSelector (allocationKind "future_allocation") "allocation"
  rejectSelector (parseTagEncoding (.str "legacy debug") "$tag") "legacy tag encoding"
  -- Diagnostic text does not become a semantic success status.
  let diagnostic := Json.mkObj [("status", .str "debug_payload"), ("text", .str "unknown")]
  discard <| must (decodeValue diagnostic "$diagnostic")
  IO.println "StrictDecoderChecks2026: successful input accepted; invalid shared references and unknown enums rejected"
