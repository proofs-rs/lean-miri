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
  for status in #["unsupported", "unknown", "incomplete", "invented"] do
    let failed := Json.mkObj [("status", .str status)]
    reject (← must (set fixture "unused_catalog" failed)) status
    reject (← must (set fixture "completeness" failed)) s!"completeness {status}"
    rejectSelector (parseStatus status) s!"status parser {status}"
  reject (← must (set fixture "unused_catalog" (Json.mkObj [("status", toJson (3 : Nat))]))) "non-string status"
  let misleadingComplete := Json.mkObj [("status", .str "complete"),
    ("unresolved_obligations", .arr #[.str "missing compiler fact"])]
  reject (← must (set fixture "completeness" misleadingComplete)) "obsolete unresolved field"
  let unusedFailure := Json.mkObj [("status", .str "unknown")]
  let unusedCatalog := Json.mkObj [("schema_version", toJson (2 : Nat)), ("nodes", .arr #[unusedFailure])]
  reject (← must (set fixture "shared_payloads" unusedCatalog)) "unreachable failed transport node"
  rejectSelector (statementVariant "FutureStatement") "statement"
  rejectSelector (terminatorVariant "FutureTerminator") "terminator"
  rejectSelector (rvalueVariant "FutureRvalue") "rvalue"
  rejectSelector (operandVariant "FutureOperand") "operand"
  rejectSelector (projectionVariant "FutureProjection") "projection"
  rejectSelector (typeShapeKind "future_type") "type shape"
  for kind in #["coroutine_witness", "parameter", "bound_type", "placeholder_type", "inference_type", "error_type"] do
    rejectSelector (typeShapeKind kind) s!"unresolved type shape {kind}"
  for kind in #["inference_variable", "error"] do
    let region := Json.mkObj [("status", .str "supported"), ("kind", .str kind)]
    rejectSelector (decodeValue region "$region" .any (some .regionKind)) s!"unresolved region {kind}"
  for kind in #["parameter", "bound", "placeholder", "inference", "error"] do
    let constant := Json.mkObj [("status", .str "supported"), ("kind", .str kind)]
    let argument := Json.mkObj [("kind", .str "const"), ("value", constant)]
    rejectSelector (decodeValue argument "$generic_argument") s!"unresolved constant {kind}"
  rejectSelector (integerTypeTag "u256") "integer kind"
  rejectSelector (layoutVariantsKind "future_layout") "layout variant"
  rejectSelector (backendReprKind "future_backend") "backend representation"
  rejectSelector (canonicalAbiKind "future_abi") "ABI"
  rejectSelector (allocationKind "future_allocation") "allocation"
  rejectSelector (parseTagEncoding (.str "legacy debug") "$tag") "legacy tag encoding"
  -- Source pool membership is a separate enum; dangling is valid metadata.
  let pool := Json.mkObj [("status", .str "dangling")]
  discard <| must (validatePayloadStatus pool "$.compiler_alloc_id_world.raw_pool[0]")
  rejectSelector (validatePayloadStatus pool "$.unrelated") "pool status outside its schema"
  -- Diagnostic text does not become a semantic success status.
  let diagnostic := Json.mkObj [("status", .str "debug_payload"), ("text", .str "unknown")]
  discard <| must (decodeValue diagnostic "$diagnostic")
  IO.println "StrictDecoderChecks2026: successful input accepted; failed statuses and unknown enums rejected"
