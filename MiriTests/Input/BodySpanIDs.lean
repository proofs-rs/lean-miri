import Miri.Input.Reader.BodySpans
import Miri.Input.Reader.RootSpan

open Lean Miri.Input.Reader

private def reference (id : Nat) : Json :=
  Json.mkObj [("$lean_miri_shared_ref", toJson id)]

private def emptyBody : Miri.Input.Body := {
  defPath := "fixture", definitionId := none, phase := .scalar .null,
  injectionPhase := none, argumentCount := 0, spreadArgument := none,
  locals := #[], blocks := #[], sourceScopes := none, payload := .null,
  promotedBodies := #[] }

def main : IO Unit := do
  let diagnostic := fun id => Json.mkObj [("status", .str "debug_payload"),
    ("rustc_debug", reference id)]
  let position := Json.mkObj [("line", toJson (1 : Nat)), ("column", toJson (0 : Nat))]
  let span := Json.mkObj [("lo", toJson (3 : Nat)), ("hi", toJson (8 : Nat)),
    ("start", position), ("end", position), ("ctxt", reference 1), ("file", reference 3)]
  let promoted := Json.mkObj [("body", Json.mkObj [("span", reference 4),
    ("preamble_def_span", span), ("basic_blocks", .arr #[])])]
  let body := Json.mkObj [("span", reference 4), ("preamble_def_span", reference 4),
    ("promoted_bodies", .arr #[promoted]), ("basic_blocks", .arr #[])]
  let dummy := Json.mkObj [("lo", toJson (0 : Nat)), ("hi", toJson (0 : Nat)),
    ("start", position), ("end", position), ("ctxt", reference 1), ("file", reference 3),
    ("is_dummy", .bool true)]
  let nodes := #[.str "ctx", diagnostic 0, .str "src.rs", diagnostic 2, span, body, dummy]
  let instanceValue := Json.mkObj [("instance_id", toJson (0 : Nat)), ("body", reference 5), ("promoted_bodies", .arr #[])]
  let .ok catalog := Catalog.parse (Json.mkObj [
      ("shared_payloads", Json.mkObj [("schema_version", toJson (2 : Nat)), ("nodes", .arr nodes)]),
      ("bodies", .arr #[reference 5]), ("instances", .arr #[instanceValue]),
      ("compiler_session_queries", Json.mkObj [("root_span", reference 6)])])
    | throw (IO.userError "catalog rejected")
  let source := {emptyBody with promotedBodies := #[⟨0, .supported, some emptyBody.toBodyCore, .null⟩]}
  let sourceInstance : Miri.Input.InstanceNode := {
    id := 0, status := .supported, kind := .instanceMir, defPath := none,
    definitionId := none, bodyInstantiation := none, bodyTemplateIsPolymorphic := none,
    instanceArgsAreMonomorphic := none, body := some source, promotedBodies := #[], payload := .null }
  let .ok (bodies, instances, table) := catalog.readSpans {} #[source] #[sourceInstance]
    | throw (IO.userError "body spans rejected")
  let some body := bodies[0]? | throw (IO.userError "body missing")
  unless body.span == some 4 && body.definitionSpan == some 4 do
    throw (IO.userError "shared span IDs changed")
  let some entry := body.promotedBodies[0]? | throw (IO.userError "promoted entry missing")
  let some child := entry.body | throw (IO.userError "promoted body missing")
  unless child.span == some 4 && child.definitionSpan == some 7 && table.size == 9 do
    throw (IO.userError "inline promoted span did not retain its table entry")
  let .ok shared := table.lookup 4 | throw (IO.userError "shared span missing")
  let .ok inlineSpan := table.lookup 7 | throw (IO.userError "inline span missing")
  unless decide (shared = inlineSpan) do throw (IO.userError "span semantic fields changed")
  let some parsedInstance := instances[0]? | throw (IO.userError "instance missing")
  let some instanceBody := parsedInstance.body | throw (IO.userError "instance body missing")
  unless instanceBody.span == some 4 && instanceBody.definitionSpan == some 4 do
    throw (IO.userError "instance span IDs missing")
  let some promoted := instanceBody.promotedBodies[0]? | throw (IO.userError "instance promoted missing")
  let some child := promoted.body | throw (IO.userError "instance promoted body missing")
  unless child.span == some 4 && child.definitionSpan == some 8 do
    throw (IO.userError "instance promoted span IDs missing")
  let .ok (root, table) := catalog.readRootSpan table | throw (IO.userError "root span rejected")
  unless root == some 6 do throw (IO.userError "root span ID lost")
  let .ok dummy := table.lookup 6 | throw (IO.userError "root span entry missing")
  unless dummy.lo == 0 && dummy.hi == 0 do throw (IO.userError "root span fields changed")
  match catalog.readSpans {} #[] #[sourceInstance] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "body table mismatch accepted")
  IO.println "body span IDs: PASS"
