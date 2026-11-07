import Miri.Input.Reader.BodyMetadata

open Lean Miri Miri.Input

private def must (value : Except ε α) [ToString ε] : IO α :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError (toString reason))

private def require (condition : Bool) (reason : String) : IO Unit :=
  unless condition do throw (IO.userError reason)

private def ref (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref", toJson id)]
private def diagnostic (value : String) : Json :=
  Json.mkObj [("status", toJson "debug_payload"), ("rustc_debug", toJson value)]
private def span (hi : Nat) : Json :=
  let position := Json.mkObj [("line", toJson (1 : Nat)), ("column", toJson (1 : Nat))]
  Json.mkObj [("lo", toJson (0 : Nat)), ("hi", toJson hi), ("start", position),
    ("end", position), ("ctxt", diagnostic "#0"), ("file", diagnostic "test.rs")]
private def evaluated : Json :=
  Json.mkObj [("kind", toJson "scalar"), ("bits_unsigned", toJson "7")]
private def constant : Json :=
  Json.mkObj [("status", toJson "supported"), ("span", ref 0),
    ("type", Json.mkObj [("type_id", toJson (0 : Nat))]), ("user_type_annotation", .null),
    ("constant", Json.mkObj [("status", toJson "supported"), ("value", ref 1),
      ("source", Json.mkObj [("kind", toJson "already_evaluated")])])]
private def success : Json :=
  Json.mkObj [("status", toJson "supported"), ("normalized_operand", ref 2), ("value", ref 1)]

private def read (result : Json) (index : Nat := 0) (checkSpan : Nat := 0) :
    Except String (BodySourceData × Reader.MIRReader.State) := do
  let checks := Json.mkObj [("status", toJson "supported"), ("typing_env", toJson "body_typing_env"),
    ("checks", .arr #[Json.mkObj [("index", toJson index), ("span", ref checkSpan), ("result", result)]])]
  let body := Json.mkObj [("basic_blocks", .arr #[]), ("source_scopes", .arr #[]), ("required_consts", .arr #[ref 2]),
    ("constant_query_context", Json.mkObj [("required_constant_checks", checks),
      ("instance_kind", Json.mkObj [("kind", toJson "item"),
        ("def_id", Json.mkObj [("crate", toJson (0 : Nat)), ("index", toJson (0 : Nat))])]),
      ("generic_args", .arr #[])])]
  let catalog ← Reader.Catalog.parse (Json.mkObj [("body", body),
    ("shared_payloads", Json.mkObj [("schema_version", toJson (2 : Nat)),
      ("nodes", .arr #[span 1,evaluated,constant,span 2])])])
  (Reader.BodyMetadataReader.read catalog ⟨1,0,#[some 4]⟩ body "body").run
    (Reader.MIRReader.initial catalog.nodes.size {})

def main : IO Unit := do
  let (body,state) ← must (read success)
  let checks : Array (Except RequiredConstantFailure RequiredConstantCheck) ← must body.requiredConstants
  require (checks.size == 1) "required constant count changed"
  let some (Except.ok check) := checks[0]? | throw (IO.userError "required constant evidence absent")
  require (check.source.index == 2 && check.normalized.index == 2) "required constant wire ID changed"
  require (check.value == .Scalar (.Int 7 4)) "required constant evaluation changed"
  require ((state.tables.constants.lookup 2).isOk) "required constant table entry absent"
  for malformed in #[read success 1, read success 0 3] do
    let (body,_) ← must malformed
    require (!body.requiredConstants.isOk) "malformed required constant evidence accepted"
  for kind in #["required_const_normalization_error", "required_const_evaluation_error", "unknown"] do
    let (body,_) ← must (read (Json.mkObj [("status", toJson "unsupported"), ("kind", toJson kind)]))
    let values : Array (Except RequiredConstantFailure RequiredConstantCheck) ← must body.requiredConstants
    let some (Except.error error) := values[0]? | throw (IO.userError "required failure was lost")
    match error with
    | .invalidProgram _ => require (kind != "unknown") "unknown required failure changed category"
    | .unsupported _ => require (kind == "unknown") "known required failure changed category"
  IO.println "required constant IDs: PASS"
