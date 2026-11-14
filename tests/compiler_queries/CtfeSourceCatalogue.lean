import Miri.Input.Decoder

open Lean Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejected (value : Except String α) (expected : String) : IO Unit :=
  match value with
  | .ok _ => throw (IO.userError s!"accepted invalid CTFE catalogue: {expected}")
  | .error error => unless error.contains expected do
      throw (IO.userError s!"wrong CTFE catalogue diagnostic: {error}; expected {expected}")
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected exported source-closure document")
  let text ← IO.FS.readFile path
  let input ← must (decodeJson text)
  unless input.document.ctfeScalarSources.size ≥ 2 do
    throw (IO.userError "closed const-function dependency sources were not captured")
  let json ← must (Json.parse text)
  let object ← must json.getObj?
  let missing := Json.mkObj ((object.toArray.filter fun (key,_) => key != "ctfe_scalar_sources").toList)
  rejected (decodeJson missing.compress) "ctfe_scalar_sources"
  rejected (decodeJson (json.setObjVal! "ctfe_scalar_sources" (toJson #[Json.mkObj []])).compress)
    "definition"
  let sources ← must ((← must (json.getObjVal? "ctfe_scalar_sources")).getArr?)
  let some source := sources[0]? | throw (IO.userError "source catalogue is empty")
  rejected (decodeJson (json.setObjVal! "ctfe_scalar_sources" (toJson (sources.push source))).compress)
    "duplicate canonical CTFE source key"
  let wrong := source.setObjVal! "span" (toJson input.document.spans.size)
  rejected (decodeJson (json.setObjVal! "ctfe_scalar_sources" (toJson #[wrong])).compress)
    "CTFE source span reference is absent"
  IO.println "PASS required CTFE catalogue, complete-document reference join, missing/malformed/duplicate/dangling controls"
