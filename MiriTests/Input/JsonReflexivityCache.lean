import Miri.Input.RuntimeMetadata

open Miri.Input

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- A deliberately invalid search tree. Its in-order fold exposes both keys,
but searching for the left key follows the wrong branch. Json object equality
therefore finds a field in its own fold that `get?` cannot find in itself. -/
private def malformedSelfUnequal : Lean.Json := Id.run do
  let impl : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json) :=
    .inner 2 "a" .null (.inner 1 "z" .null .leaf .leaf) .leaf
  let dmap : Std.DTreeMap.Raw String (fun _ => Lean.Json) := ⟨impl⟩
  let raw : Std.TreeMap.Raw String Lean.Json := ⟨dmap⟩
  return .obj raw

def main : IO Unit := do
  let shared : Lean.Json := .mkObj [("nested", .arr #[.str "same", .num 3])]
  let certificate := RuntimeMetadata.JsonReflexivity.prepare (left := shared)
  check certificate.reflexive.isSome "same-object certificate was not prepared"
  check (certificate.matchesRight shared) "same-object comparison changed"
  check (certificate.matchesLeft shared) "same-object reverse comparison changed"

  let copy : Lean.Json := .mkObj [("nested", .arr #[.str "same", .num 3])]
  check (shared == copy) "test setup expected separate JSON values to compare equal"
  check (certificate.matchesRight copy) "deep-equal separate JSON did not match"
  check (certificate.matchesLeft copy) "deep-equal reverse JSON did not match"

  let different : Lean.Json := .mkObj [("nested", .arr #[.str "different", .num 3])]
  check (!(certificate.matchesRight different)) "mismatched JSON unexpectedly matched"
  check (!(certificate.matchesLeft different)) "mismatched reverse JSON unexpectedly matched"

  let malformed := malformedSelfUnequal
  check (!(malformed == malformed)) "malformed self-nonreflexive JSON test setup changed"
  let malformedCertificate := RuntimeMetadata.JsonReflexivity.prepare (left := malformed)
  check malformedCertificate.reflexive.isNone "non-reflexive JSON received a reflexivity certificate"
  check (!(malformedCertificate.matchesRight malformed)) "fallback right comparison changed malformed behavior"
  check (!(malformedCertificate.matchesLeft malformed)) "fallback left comparison changed malformed behavior"
  IO.println "JsonReflexivityCache PASS: identical, deep-equal, mismatched and non-reflexive JSON comparisons"
