import Miri.Input.EvalPreparation
import Miri.Input.CompilerFunctionFacts
import Miri.Input.CompilerValueConstants

/-! Fresh numeric-input regression for demanded compiler metadata. Supported
signature queries and every decoded FnAbi must survive direct table lookup;
provider and allocation preparation must succeed. This finite preparation
check executes no guest MIR and proves no Rust safety property. -/
open Lean Miri.Input
set_option maxRecDepth 32768
set_option maxHeartbeats 0

private def must (result : Except String α) : IO α := do
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def natural (value : Nat) : Json := toJson value

def main (args : List String) : IO Unit := do
  let (path, checkForeignStatic) ← match args with
    | [path] => pure (path, false)
    | [path, "foreign-static"] => pure (path, true)
    | _ => throw (IO.userError "expected a fresh exported input and optional foreign-static mode")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let program ← must (lowerCoreProgram decoded.document)
  let prepared ← must (CompilerProviders.prepare program)
  if checkForeignStatic then
    let some selected := prepared.externStatics.selected.find?
        (fun entry => entry.symbol == "FOREIGN_STATIC_TARGET") |
      throw (IO.userError "fresh fixture did not exercise selected foreign-static lookup")
    unless selected.winner.result.isOk && selected.winner.allocation.isSome do
      throw (IO.userError s!"selected foreign-static allocation lookup failed: {reprStr selected.winner.result}")
  let functionRecords ← must ((← must (prepared.program.input.raw.getObjVal? "compiler_function_facts")).getObjVal? "types" >>= Json.getArr?)
  let mut expectedSignatures := 0
  for record in functionRecords do
    let id ← must ((← must (record.getObjVal? "type_id")).getNat?)
    let query ← must (record.getObjVal? "signature_query")
    let supported := query.getNat?.isOk
    let actual := CompilerFunctionFacts.signature prepared.functions id
    unless actual.isOk == supported do
      let detail := match actual with
        | .error reason => reason
        | .ok _ => "unexpected successful signature"
      throw (IO.userError s!"function signature status changed for compiler type {id}: {detail}")
    if supported then expectedSignatures := expectedSignatures + 1
  let mut checkedAbis := 0
  for abi in decoded.document.functionAbis do
    discard <| must (CallResolution.functionAbiJson prepared.runtime abi.payload)
    checkedAbis := checkedAbis + 1
  let calls := prepared.lifecycle.calls.calls
  let mut checkedCalls := 0
  let mut checkedCallAbis := 0
  for entry in calls.entries do
    let some body := calls.program.bundle.bodies[entry.site.bodyIndex]? |
      throw (IO.userError "prepared call site has no owning body")
    let blocks ← must ((← must (body.input.payload.getObjVal? "basic_blocks")).getArr?)
    let some block := blocks[entry.site.block]? |
      throw (IO.userError "prepared call site has no source block")
    let source ← must (block.getObjVal? "terminator" >>= fun term => term.getObjVal? "kind" >>= fun kind => kind.getObjVal? "resolution")
    let kind := (source.getObjValAs? String "kind").toOption.getD ""
    if ["resolved_instance", "virtual_dispatch"].contains kind then
      let resolution ← must (entry.outcome.mapError fun reason =>
        s!"supported source call body[{entry.site.bodyIndex}].block[{entry.site.block}] failed: {reason}")
      checkedCalls := checkedCalls + 1
      if ((source.getObjVal? "fn_abi").bind Json.getNat?).isOk then
        discard <| must (resolution.abi.mapError fun reason =>
          s!"supported source call ABI failed: {reason}")
        checkedCallAbis := checkedCallAbis + 1
  let summary := Json.mkObj [
    ("checked_calls", natural checkedCalls),
    ("checked_call_abis", natural checkedCallAbis),
    ("call_resolution_obligations", natural calls.obligations.size),
    ("types", natural prepared.program.input.types.size),
    ("allocations", natural prepared.program.input.allocations.size),
    ("bodies", natural prepared.program.bundle.bodies.size),
    ("definitions", natural prepared.program.compilerTables.definitions.size),
    ("spans", natural prepared.program.compilerTables.spans.size),
    ("type_constants", natural prepared.program.compilerTables.typeConstants.size),
    ("functions", natural prepared.functions.functions.size),
    ("successful_signatures", natural expectedSignatures),
    ("checked_abis", natural checkedAbis),
    ("pointer_abis", natural prepared.functions.pointerAbis.size),
    ("successful_pointer_abis", natural (prepared.functions.pointerAbis.filter (·.result.isOk)).size),
    ("constant_evidence", natural prepared.constants.evidence.size),
    ("constant_obligations", natural prepared.constants.obligations.size)]
  IO.println summary.compress
  for issue in prepared.constants.obligations do
    IO.println s!"constant_obligation: {issue.path}: {issue.message}"
  let attempt := EvalPreparation.prepare program
  match attempt.outcome with
  | .ok _ => IO.println "eval_preparation=ok"
  | .error reason => throw (IO.userError s!"eval_preparation failed: {reason}")
