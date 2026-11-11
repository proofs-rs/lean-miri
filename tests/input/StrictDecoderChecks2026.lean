import MiriTests.Input.JsonFixtures
import Miri.Input.Decoder

open Lean Miri.Input Miri.Input.DecoderValues

private def must (outcome : Except String α) : IO α :=
  match outcome with | .ok value => pure value | .error message => throw (IO.userError message)
private def string (value : String) := Json.renderString value
private def object (fields : List (String × String)) :=
  "{" ++ String.intercalate "," (fields.map fun (key,value) => string key ++ ":" ++ value) ++ "}"
private def arr (values : Array String) := "[" ++ String.intercalate "," values.toList ++ "]"
private def get (source key : String) : Except String String := do
  return (← (← JsonFixtures.parse source).field key).text
private def array (source : String) : Except String (Array String) := do
  return (← (← JsonFixtures.parse source).array).map (·.text)
private def set (source key child : String) : Except String String := do
  let fields ← (← JsonFixtures.parse source).object
  let retained := fields.filterMap fun (name,value) =>
    if name == key then none else some (name,value.text)
  pure (object ((key,child)::retained.toList))
private def rejects (outcome : Except String α) (label : String) : IO Unit :=
  if outcome.isOk then throw (IO.userError s!"{label}: invalid input was accepted") else pure ()

private def replaceBodyNode (fixture : String) (kind : String) (terminator : Bool) : Except String String := do
  let bodies ← array (← get fixture "bodies")
  let some body := bodies[0]? | throw "fixture has no body"
  let blocks ← array (← get body "basic_blocks")
  let some block := blocks[0]? | throw "fixture has no block"
  let term ← get block "terminator"
  let info ← get term "source_info"
  let statementKinds ← array (← get fixture "statement_kinds")
  let fixture ← if terminator then pure fixture else set fixture "statement_kinds" (arr (statementKinds.push kind))
  let node := object [("source_info",info),("kind",if terminator then kind else toString statementKinds.size)]
  let block ← if terminator then set block "terminator" node else set block "statements" (arr #[node])
  let body ← set body "basic_blocks" (arr (blocks.set! 0 block))
  set fixture "bodies" (arr (bodies.set! 0 body))

def main : IO Unit := do
  let fixture ← IO.FS.readFile "tests/input/fixtures/strict-unit.json"
  let full ← must (decodeJson fixture)
  unless full.document.types.size == 20 && full.document.layouts.size == 20 do
    throw (IO.userError "typed table definitions were discarded")
  let types ← must (array (← must (get fixture "types")))
  let some firstType := types[0]? | throw (IO.userError "fixture has no type")
  let oversizedArray := object [("kind",string "array"),("element","0"),("length","0"),
    ("constructor_identity",object [("count",toString (2^64 : Nat)),("canonical_value_constructor","true")])]
  -- These complete rows must fail at the parser, before any table-wide join.
  rejects (JsonReader.run parseTypeNode (← must (set firstType "shape" oversizedArray))) "row-local array count"
  rejects (JsonReader.run parseTagEncoding
    r#"{"kind":"niche","untagged_variant":0,"niche_variants":{"start":2,"end":1},"niche_start":"0"}"#)
    "row-local reversed niche range"
  let instances ← must (array (← must (get fixture "instances")))
  let some firstInstance := instances[0]? | throw (IO.userError "fixture has no instance")
  rejects (JsonReader.run (parseInstance "$instance") (← must (set firstInstance "def_id" "99999")))
    "row-local instance definition identity"
  let badType ← must (set firstType "layout" "99999")
  rejects (decodeJson (← must (set fixture "types" (arr (types.set! 0 badType))))) "out of bounds layout"
  let invalidScope := object [("kind",string "future_scope"),
    ("semantics",string "structural_export_closure_only"),("roots","[]")]
  let invalidScopeInput ← must (set fixture "selected_scope" invalidScope)
  match decodeJson invalidScopeInput with
  | .error message =>
    unless message.contains "selected_scope" do throw (IO.userError s!"wrong scope diagnostic: {message}")
  | .ok _ => throw (IO.userError "invalid selected scope was accepted")
  let malformedOnly ← must (set fixture "compiler_predicate_queries" "[null]")
  let expectedTableError ← match decodeJson malformedOnly with
    | .error message => pure message
    | .ok _ => throw (IO.userError "malformed predicate definition was accepted")
  let malformedTable ← must (set invalidScopeInput "compiler_predicate_queries" "[null]")
  match decodeJson malformedTable with
  | .error message =>
    unless message == expectedTableError do
      throw (IO.userError s!"malformed table did not precede scope validation: {message}")
  | .ok _ => throw (IO.userError "malformed predicate definition was accepted")

  let badStatement := object [("variant",string "FutureStatement")]
  rejects (decodeJson (← must (replaceBodyNode fixture badStatement false))) "statement"
  let badTerminator := object [("variant",string "FutureTerminator")]
  rejects (decodeJson (← must (replaceBodyNode fixture badTerminator true))) "terminator"
  let place := object [("local","0"),("type","0"),("projection","[]")]
  let assign (rvalue : String) := object [("variant",string "Assign"),("place",place),("rvalue",rvalue)]
  rejects (decodeJson (← must (replaceBodyNode fixture (assign (object [("kind",string "FutureRvalue")])) false))) "rvalue"
  let operand := object [("kind",string "FutureOperand")]
  rejects (decodeJson (← must (replaceBodyNode fixture (assign (object [("kind",string "Use"),("operand",operand),
    ("retag",object [("kind",string "no"),("performs_retag","false")])])) false))) "operand"
  let projection := object [("local","0"),("type","0"),("projection",arr #[object [("kind",string "FutureProjection")]])]
  rejects (JsonReader.run DecodeMIR.place projection) "projection"
  rejects (typeShapeKind "future_type") "type shape"
  for kind in #["coroutine_witness", "parameter", "bound_type", "placeholder_type", "inference_type", "error_type"] do
    rejects (typeShapeKind kind) s!"unresolved type shape {kind}"
  for kind in #["inference_variable", "error"] do
    rejects (JsonReader.run GenericArgsCodec.region (object [("kind",string kind)])) s!"unresolved region {kind}"
  for kind in #["parameter", "bound", "placeholder", "inference", "error"] do
    let constant := object [("kind",string kind)]
    let argument := arr #[object [("kind",string "const"),("value",constant)]]
    rejects (JsonReader.run GenericArgsCodec.decode argument) s!"unresolved constant {kind}"
  rejects (integerTypeTag "u256") "integer kind"
  rejects (layoutVariantsKind "future_layout") "layout variant"
  rejects (backendReprKind "future_backend") "backend representation"
  rejects (canonicalAbiKind "future_abi") "ABI"
  rejects (JsonReader.run (parseAbiTag "$abi") "{\"kind\":\"Rust\",\"variant\":\"C\"}") "ambiguous ABI tag"
  rejects (allocationKind "future_allocation") "allocation"
  rejects (JsonReader.run (parseTagEncoding "$tag") (string "legacy debug")) "legacy tag encoding"
  IO.println "StrictDecoderChecks2026: typed references, unknown MIR constructors and unresolved compiler values rejected"
