import Miri.Input.Decoder

open Lean Miri.Input

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def field (value : Json) (key : String) : IO Json := do
  match value.getObjVal? key with
  | .ok result => pure result
  | .error error => throw (IO.userError s!"missing `{key}`: {error}")

private def textField (value : Json) (key : String) : IO String := do
  let result ← field value key
  match result.getStr? with
  | .ok text => pure text
  | .error error => throw (IO.userError s!"`{key}` must be a string: {error}")

private def boolField (value : Json) (key : String) : IO Bool := do
  let result ← field value key
  match result.getBool? with
  | .ok flag => pure flag
  | .error error => throw (IO.userError s!"`{key}` must be Boolean: {error}")

private def obligationsJson (obligations : Array Obligation) : Json :=
  Json.arr (obligations.map fun item => Json.mkObj [
    ("path", toJson item.path), ("message", toJson item.message)])

private def acceptedSummary (ready : Bool) (obligations : Array Obligation) : Json :=
  Json.mkObj [
    ("kind", toJson ("ok" : String)),
    ("readiness", Json.bool ready),
    ("obligations", obligationsJson obligations)]

private def decodeSummary (text : String) : Except String Json := do
  let decoded ← decodeJson text
  pure (acceptedSummary decoded.executionInput.isSome decoded.blockingObligations)

private def readCase (directory name : String) : IO String :=
  IO.FS.readFile s!"{directory}/{name}.json"

private def caseNames : List String := [
  "genuine-mir-features", "genuine-fresh", "valid-permuted-dense",
  "duplicate-and-range-first", "out-of-range-type-id", "negative-type-id",
  "malformed-table-type-id", "dangling-type", "dangling-allocation", "dangling-instance",
  "malformed-type-reference", "malformed-allocation-reference", "malformed-instance-reference",
  "nested-debug-payload-skips-references", "empty-allocations", "empty-instances"]

private def capture (directory output : String) : IO Unit := do
  let mut results := #[]
  for name in caseNames do
    let text ← readCase directory name
    let outcome := match decodeSummary text with
      | .ok summary => summary
      | .error message => Json.mkObj [
          ("kind", toJson ("error" : String)), ("error", toJson message)]
    results := results.push (name, outcome)
    IO.println s!"CAPTURE {name}: {outcome.compress}"
  IO.FS.writeFile output (Json.mkObj results.toList).compress

private def checkCase (directory : String) (expected : Json) (name : String) : IO Unit := do
  let text ← readCase directory name
  let wanted ← field expected name
  let kind ← textField wanted "kind"
  match decodeJson text, decodeRuntimeJson text, kind with
  | .error fullError, .error runtimeError, "error" => do
    let expectedError ← textField wanted "error"
    check (fullError == expectedError)
      s!"{name}: decodeJson changed exact error; expected={expectedError}; actual={fullError}"
    check (runtimeError == expectedError)
      s!"{name}: decodeRuntimeJson differs from baseline error; expected={expectedError}; actual={runtimeError}"
    IO.println s!"PASS {name}: exact error {fullError}"
  | .ok full, .ok runtime, "ok" => do
    let expectedReady ← boolField wanted "readiness"
    let expectedObligations ← field wanted "obligations"
    let fullSummary := acceptedSummary full.executionInput.isSome full.blockingObligations
    let runtimeSummary := acceptedSummary runtime.executionInput.isSome runtime.blockingObligations
    check (fullSummary == wanted)
      s!"{name}: decodeJson readiness/ordered obligations changed from baseline"
    check (runtimeSummary == wanted)
      s!"{name}: decodeRuntimeJson readiness/ordered obligations changed from baseline"
    check (full.blockingObligations == runtime.blockingObligations)
      s!"{name}: ordered blocking obligations differ between decoders"
    check (full.executionInput.isSome == runtime.executionInput.isSome)
      s!"{name}: execution readiness differs between decoders"
    check (full.executionInput.isSome == expectedReady && obligationsJson full.blockingObligations == expectedObligations)
      s!"{name}: readiness or obligations differ from stored baseline"
    IO.println s!"PASS {name}: accepted; obligations={full.blockingObligations.size}; readiness={full.executionInput.isSome}"
  | .error error, .ok _, _ => throw (IO.userError s!"{name}: full decoder rejected but runtime decoder accepted: {error}")
  | .ok _, .error error, _ => throw (IO.userError s!"{name}: runtime decoder rejected but full decoder accepted: {error}")
  | _, _, "error" => throw (IO.userError s!"{name}: expected a hard error")
  | _, _, "ok" => throw (IO.userError s!"{name}: expected acceptance")
  | _, _, other => throw (IO.userError s!"{name}: unknown expected outcome `{other}`")

def main (args : List String) : IO Unit := do
  match args with
  | [directory, "--capture", output] => capture directory output
  | [directory, expectedPath] => do
    let expectedText ← IO.FS.readFile expectedPath
    let expected ← match Json.parse expectedText with
      | .ok value => pure value
      | .error error => throw (IO.userError s!"invalid expected-results JSON: {error}")
    for name in caseNames do checkCase directory expected name
  | _ => throw (IO.userError "usage: DecoderIdChecks2026 <case-directory> <baseline-results.json> | <case-directory> --capture <output.json>")
