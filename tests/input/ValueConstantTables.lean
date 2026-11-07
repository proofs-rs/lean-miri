import Miri.Input.Reader.ValueConstants

open Lean Miri.Input Miri.Input.Reader

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def entry (rows : Array α) (index : Nat) : IO α :=
  match rows[index]? with
  | some value => pure value
  | none => throw (IO.userError "constant row absent")
private def reference (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref",toJson id)]
private def ty (id : Nat) : Json := Json.mkObj [("type_id",toJson id)]
private def record (input result : Json) (bits : String := "42") (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("status",toJson "supported"),("typing_env",toJson "fully_monomorphized"),
    ("input_type",input),("result_type",result),
    ("value",Json.mkObj [("kind",toJson "scalar"),("bits_unsigned",toJson bits)])] ++ extra)
private def failed (status reason debug : String) : Json := Json.mkObj [
  ("status",toJson status),("reason",toJson reason),("debug",toJson debug),
  ("typing_env",toJson "fully_monomorphized"),("input_type",ty 0)]
private def catalog (key : String) (records nodes : Array Json) : IO Catalog := do
  must (Catalog.parse (Json.mkObj [("shared_payloads",Json.mkObj [("schema_version",toJson (2 : Nat)),
    ("nodes",Json.arr nodes)]),(key,Json.arr records)]))
private def span (context : String) : Json :=
  let position := Json.mkObj [("line",toJson (1 : Nat)),("column",toJson (1 : Nat))]
  let diagnostic := fun text => Json.mkObj [("status",toJson "debug_payload"),("rustc_debug",toJson text)]
  Json.mkObj [("lo",toJson (10 : Nat)),("hi",toJson (20 : Nat)),("start",position),("end",position),
    ("ctxt",diagnostic context),("file",diagnostic "file")]
private def caller (source : Json) (result : Nat) (bits : String) (debug : String) : Json := Json.mkObj [
  ("span",source),("result_type",ty result),("status",toJson "supported"),("debug",toJson debug),
  ("value",Json.mkObj [("kind",toJson "scalar"),("bits_unsigned",toJson bits)])]

def main : IO Unit := do
  let shared := record (reference 0) (reference 0)
  let source ← catalog "compiler_type_name_constants" #[
    reference 1,record (ty 0) (ty 0),record (ty 0) (ty 0) "42" [("extra",toJson true)],
    record (ty 0) (ty 0) "43",record (ty 0) (ty 1),record (ty 1) (ty 0),
    failed "unsupported" "first" "A",failed "unsupported" "first" "B",
    failed "unsupported" "second" "A",failed "incomplete" "first" "A"] #[ty 0,shared]
  let rows ← must (ValueConstantReader.typeNames source ⟨2,0,#[some 4,some 4]⟩)
  let get := entry rows
  let first ← get 0
  let same ← get 1
  let debugOnly ← get 2
  let differentValue ← get 3
  let differentType ← get 4
  let differentInput ← get 5
  unless first.inputType == some 0 && first.result == .ok (0,.Scalar (.Int 42 4)) &&
      first.sourceKey == same.sourceKey && first.sourceKey == debugOnly.sourceKey &&
      first.sourceKey != differentValue.sourceKey && first.sourceKey != differentType.sourceKey &&
      first.sourceKey != differentInput.sourceKey do
    throw (IO.userError "typed type-name duplicate class lost query/value/type distinctions or retained debug noise")
  let failedFirst ← get 6
  let failedDebug ← get 7
  let failedReason ← get 8
  let failedStatus ← get 9
  unless failedFirst.sourceKey == failedDebug.sourceKey && failedFirst.sourceKey != failedReason.sourceKey &&
      failedFirst.sourceKey != failedStatus.sourceKey && failedFirst.result.toOption.isNone do
    throw (IO.userError "meaningful failed status/reason distinctions or debug coalescing changed")
  let source ← catalog "compiler_caller_location_constants" #[
    caller (span "A") 0 "42" "first",caller (span "A") 0 "42" "second",
    caller (span "B") 0 "42" "first",caller (span "A") 0 "43" "first",
    caller (span "A") 1 "42" "first",Json.mkObj []] #[]
  let rows ← must (ValueConstantReader.callerLocations source ⟨2,0,#[some 4,some 4]⟩)
  let get := entry rows
  let first ← get 0
  let debugOnly ← get 1
  let differentSpan ← get 2
  let differentValue ← get 3
  let differentType ← get 4
  let malformed ← get 5
  unless first.sourceKey == debugOnly.sourceKey && first.sourceKey != differentSpan.sourceKey &&
      first.sourceKey != differentValue.sourceKey && first.sourceKey != differentType.sourceKey &&
      first.span != differentSpan.span && malformed.span.toOption.isNone do
    throw (IO.userError "typed caller-location classes alias a full-span/value/type collision")
