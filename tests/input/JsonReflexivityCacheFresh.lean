import Miri.Input.RuntimeMetadata

open Miri.Input

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

private def parseJson (text : String) : IO Lean.Json :=
  match Lean.Json.parse text with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"invalid test JSON: {error}")

def main : IO Unit := do
  let sourceText ← IO.FS.readFile "tests/input/json-reflexivity-cache.json"
  let source ← parseJson sourceText
  let candidateText ← IO.FS.readFile "tests/input/json-reflexivity-cache.json"
  let candidate ← parseJson candidateText
  check (source == candidate) "independently parsed documents were not deeply equal"

  let certificate := RuntimeMetadata.JsonReflexivity.prepare (left := source)
  check certificate.reflexive.isSome "parsed document did not receive a reflexivity certificate"
  check (certificate.matchesRight candidate) "deep-equal parsed JSON did not match"
  check (certificate.matchesLeft candidate) "deep-equal reverse parsed JSON did not match"

  let uncached : Option (RuntimeMetadata.JsonReflexivity source) := none
  check (RuntimeMetadata.JsonReflexivity.matchesRightOr uncached candidate == (source == candidate))
    "optional uncached comparison changed the original equality result"

  let mismatch ← parseJson "{\"nested\":[\"different\",3]}"
  check (!(certificate.matchesRight mismatch)) "mismatched parsed JSON unexpectedly matched"
  check (!(certificate.matchesLeft mismatch)) "mismatched parsed JSON matched in reverse"
  check (!(RuntimeMetadata.JsonReflexivity.matchesRightOr uncached mismatch))
    "optional uncached mismatch unexpectedly matched"

  IO.println "JsonReflexivityCacheFresh PASS: independently parsed deep equality, mismatch and absent-cache fallback"
