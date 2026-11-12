import MiriTests.Input.LegacyFixture
import Miri.Input
import Miri.Input.CompilerNativeSignatures

/-! Finite provider checks on a fresh coroutine export. Missing native-callback
FnSig facts remain errors; ordinary runtime FnAbi facts are separate and retained.
This checks query boundaries, not MIR execution or arbitrary coroutine safety. -/
open Miri.Input Miri.Interpreter
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "fresh schema-12 coroutine input required")
  let input ← must (decodeFixture (← IO.FS.readFile path))
  let some coverage := input.document.coroutineCoverage | throw (IO.userError "missing coroutine coverage")
  check (!coverage.coroutines.isEmpty) "fixture has no coroutine body"
  let prepared ← must (CompilerProviders.prepare (← must (lowerProgram input.document)))
  for row in coverage.coroutines do
    let body ← must (SourceMir.metadata input.document row.ownerBody)
    let callee := body.instanceId
    check (!(input.document.queries.nativeSignatures.any (·.instanceId == callee)))
      "a coroutine acquired a fabricated native callback signature"
    match CompilerNativeSignatures.query prepared callee with
    | .ok _ => throw (IO.userError "native callback query accepted a coroutine without an exact compiler FnSig")
    | .error error =>
      check ((error.splitOn "missing exact compiler native signature query").length > 1) s!"wrong native callback boundary: {error}"
    discard <| must (CompilerInstanceAbi.abiOfInstance prepared.lifecycle.instances callee #[])
  let some ordinary := input.document.queries.nativeSignatures.find? fun row =>
      row.query == "instantiate_bound_regions_with_erased(fn_sig(instance.def_id()).instantiate(instance.args))" |
    throw (IO.userError "fixture has no normal native FnSig control")
  discard <| must (CompilerNativeSignatures.query prepared ordinary.instanceId)
  let queries := prepared.program.input.queries
  let without := {queries with nativeSignatures := queries.nativeSignatures.filter (·.instanceId != ordinary.instanceId)}
  let program := {prepared.program with input := {prepared.program.input with queries := without}}
  check (!(CompilerNativeSignatures.query {prepared with program} ordinary.instanceId).isOk)
    "missing normal native callback signature was accepted"
  check (queries.nativeSignatures.any (·.query == "instantiate_bound_regions_with_erased(closure_args.sig())"))
    "normal closure signature facts were dropped with coroutine signatures"
  IO.println s!"PASS {coverage.coroutines.size} coroutine native-FnSig failures with exact runtime FnAbi retained; normal function/closure controls retained"
