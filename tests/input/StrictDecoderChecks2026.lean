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
  if (decodeJson input.compress).isOk then
    throw (IO.userError s!"{label}: failed input was accepted")

private def rejectSelector (outcome : Except String α) (label : String) : IO Unit :=
  if outcome.isOk then throw (IO.userError s!"{label}: unknown enum was accepted") else pure ()

def main : IO Unit := do
  let fixture ← must (Json.parse (← IO.FS.readFile "tests/input/fixtures/strict-unit.json"))
  let full ← must (decodeJson fixture.compress)
  unless full.document.types.size == 3 && full.document.layouts.size == 3 do
    throw (IO.userError "typed table definitions were discarded")
  reject (← must (set fixture "shared_payloads" (Json.mkObj []))) "obsolete generic graph transport"
  let types ← must ((fixture.getObjVal? "types").bind Json.getArr?)
  let badType ← must (set types[0]! "layout" (toJson (99999 : Nat)))
  reject (← must (set fixture "types" (.arr (types.set! 0 badType)))) "out of bounds layout"
  -- Table decoding precedes downstream scope validation.
  let invalidScope := Json.mkObj [("kind", .str "future_scope"),
    ("semantics", .str "structural_export_closure_only"), ("roots", .arr #[])]
  let invalidScopeInput ← must (set fixture "selected_scope" invalidScope)
  match decodeJson invalidScopeInput.compress with
  | .error message =>
    unless message == "$.selected_scope.kind: unrecognized selected-scope kind `future_scope`" do
      throw (IO.userError s!"isolated scope diagnostic changed: {message}")
  | .ok _ => throw (IO.userError "invalid selected scope was accepted")
  let malformedTable ← must (set invalidScopeInput "compiler_predicate_queries" (.arr #[.null]))
  match decodeJson malformedTable.compress with
  | .error message =>
    unless message == "$predicate: missing/invalid field `normalization` (object expected)" do
      throw (IO.userError s!"malformed table did not precede scope validation: {message}")
  | .ok _ => throw (IO.userError "malformed predicate definition was accepted")
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
  IO.println "StrictDecoderChecks2026: successful input accepted; invalid typed references and unknown enums rejected"
