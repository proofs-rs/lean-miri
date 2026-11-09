import Miri.Input.JsonReader

open Miri.Input.JsonReader

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def expectOk (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private structure Example where
  count : Option Nat := none
  label : Option String := none
  values : Option (Array Bool) := none
  deriving BEq

private def parseExample : Parser Example := do
  let value ← object ({} : Example) fun v key => do
    match key with
    | "count" => return {v with count := some (← natural)}
    | "label" => return {v with label := some (← string)}
    | "values" => return {v with values := some (← array boolean)}
    | _ => skipValue; return v
  let _ ← required value.count "count"
  let _ ← required value.label "label"
  let _ ← required value.values "values"
  return value

#eval show IO Unit from do
  let a ← expectOk (run parseExample "{\"count\":7,\"label\":\"é😃\",\"values\":[true,false]}")
  let b ← expectOk (run parseExample "{\"values\":[true,false],\"ignored\":{\"a\":[null,1.5,\"ok\"]},\"label\":\"é\\uD83D\\uDE03\",\"count\":7}")
  check (a == b) "field order or unknown data changed typed result"
  check ((← expectOk (run integer "-5")) == -5) "signed integer"
  check ((← expectOk (run natural "1e2")) == 100) "positive exponent"
  check ((← expectOk (run (nullable natural) "null")).isNone) "nullable"
  for source in ["-1", "1.0", "1.25", "null", "\"2\""] do
    check (!(run natural source).isOk) s!"invalid natural accepted: {source}"
  for source in ["{\"count\":7,\"count\":8,\"label\":\"x\",\"values\":[]}",
      "{\"count\":7,\"label\":\"x\",\"values\":[],\"other\":1,\"other\":2}",
      "{\"label\":\"x\",\"values\":[]}",
      "{\"count\":null,\"label\":\"x\",\"values\":[]}"] do
    check (!(run parseExample source).isOk) s!"invalid schema accepted: {source}"
  for source in ["", " ", "[", "{", "[1,]", "{\"x\":1,}", "[1 2]", "{\"x\" 1}",
      "01", "-", "1.", "1e", "1e+", "true false", "nullx", "\"unterminated",
      "\"\\x\"", "\"\\u12q4\"", "\"line\nfeed\"", "{\"ignored\":[0,{\"x\":tru}]}",
      "{\"x\":1,\"x\":2}"] do
    check (!(run skipValue source).isOk) s!"invalid JSON accepted: {source}"
