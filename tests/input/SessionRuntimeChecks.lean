import Miri.Input.Reader.SessionMetadata

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)
private def ref (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref",toJson id)]
private def check (kind : Json) : Json :=
  Json.mkObj [("kind",kind),("status",ref 0),("enabled",ref 1)]
private def read (rows : Json) : Except String SessionMetadataData := do
  let catalog ← Reader.Catalog.parse (Json.mkObj [
    ("shared_payloads",Json.mkObj [("schema_version",toJson (2 : Nat)),
      ("nodes",.arr #[toJson "supported",toJson true,check (toJson "ub_checks")])]),
    ("compiler_session_queries",Json.mkObj [("runtime_checks",rows)])])
  Reader.SessionMetadataReader.session catalog

def main : IO Unit := do
  let data ← must (read (.arr #[ref 2,check (toJson "contract_checks"),check (toJson "overflow_checks")]))
  let actual ← must data.runtimeChecks
  unless actual == #[(Miri.MIR.RuntimeChecks.UbChecks,true),(.ContractChecks,true),(.OverflowChecks,true)] do
    throw (IO.userError "session runtime-check fields changed")
  -- Independent session queries remain deferred when unrelated fields are absent.
  unless !data.internalTargetFeatures.isOk && !data.isLikeWasm.isOk do
    throw (IO.userError "missing independent session metadata was synthesized")
  for rows in #[.arr #[ref 2,ref 2],.arr #[check (toJson "unknown")]] do
    let data ← must (read rows)
    unless !data.runtimeChecks.isOk do throw (IO.userError "invalid runtime-check catalog accepted")
  IO.println "session runtime checks: PASS"
