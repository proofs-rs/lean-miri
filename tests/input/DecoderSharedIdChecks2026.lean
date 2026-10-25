import Miri.Input.Decoder

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def set (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (Json.mkObj ((key, child) :: fields.toList.filter (fun item => item.1 != key)))

private def ref (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref", toJson id)]

private def repeated (source leaf : Json) : Except String Json := do
  let parent := Json.mkObj [("child", ref 0)]
  let source ← set source "shared_payloads" (Json.mkObj [
    ("schema_version", toJson (2 : Nat)), ("nodes", .arr #[leaf, parent])])
  let source ← set source "synthetic_shared_a" (ref 1)
  let source ← set source "synthetic_shared_b" (ref 1)
  set source "synthetic_shared_c" (ref 0)

private def rejects (name : String) (source : Json) (expected : String) : IO Unit := do
  let text := source.compress
  match decodeJson text, decodeRuntimeJson text with
  | .error full, .error runtime =>
    check (full == expected && runtime == expected)
      s!"{name}: expected={expected}; full={full}; runtime={runtime}"
  | _, _ => throw (IO.userError s!"{name}: both decoders must reject")
  IO.println s!"PASS {name}: {expected}"

def main (args : List String) : IO Unit := do
  let directory ← match args with
    | [directory] => pure directory
    | _ => throw (IO.userError "expected directory containing transported mini schema-3 cases")
  let valid ← must (Json.parse (← IO.FS.readFile s!"{directory}/valid-permuted-dense.json"))
  let source ← must (repeated valid (Json.mkObj [("type_id", toJson (0 : Nat))]))
  let full ← must (decodeJson source.compress)
  let runtime ← must (decodeRuntimeJson source.compress)
  check (full.executionInput.isSome && runtime.executionInput.isSome &&
    full.blockingObligations.isEmpty && runtime.blockingObligations.isEmpty)
    "shared valid type references changed acceptance/readiness"
  check (full.document.sharedNodes.size == 2 && runtime.document.sharedNodes.size == 2)
    "valid repeated graph did not exercise catalog resolution"
  IO.println "PASS repeated-valid-ID: shared parent and leaf accepted by both decoders"
  let huge : Nat := 2^100
  let source ← must (repeated valid (Json.mkObj [("type_id", toJson huge)]))
  rejects "repeated-dangling-ID-first-path" source
    s!"$.synthetic_shared_a.child: dangling type reference {huge}"
  let source ← must (repeated valid (Json.mkObj [("type_id", .str "bad")]))
  rejects "repeated-malformed-ID-first-path" source
    "$.synthetic_shared_a.child.type_id: malformed type reference (Natural number expected)"
  let duplicates ← must (Json.parse (← IO.FS.readFile s!"{directory}/duplicate-and-range-first.json"))
  let source ← must (repeated duplicates (Json.mkObj [("type_id", toJson huge)]))
  rejects "duplicate-table-before-shared-dangling-ID" source "type IDs: duplicate IDs"
  IO.println "SharedIdReferenceChecks: 4 schema-3 shared-ID cases passed"
