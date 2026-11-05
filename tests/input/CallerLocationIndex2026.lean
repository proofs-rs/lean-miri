import Miri.Input.EvalPreparation
import Miri.Input.CompilerValueConstants

open Lean Miri.Input Miri.Interpreter

#print axioms CompilerSpanInterner.sameSpansAs_eq

theorem callerLocationSpanComparison_eq (result base : CompilerSpanInterner) :
    result.sameSpansAs base = (result.getTables.spans == base.getTables.spans) := by
  rw [CompilerSpanInterner.sameSpansAs_eq]
  exact Bool.beq_comm

#print axioms callerLocationSpanComparison_eq


private def must (value : Except String α) : IO α :=
  match value with | .ok x => pure x | .error e => throw (IO.userError e)
private def set (j : Json) (key : String) (value : Json) : Json :=
  match j with
  | .obj fields => Json.mkObj ((key,value) :: fields.toList.filter (fun e => e.1 != key))
  | _ => Json.mkObj [(key,value)]
private def withRows (p : CompilerProviders.Prepared) (rows : Json) : CompilerProviders.Prepared :=
  let raw := set p.program.input.raw "compiler_caller_location_constants" rows
  let program := {p.program with input := {p.program.input with raw, allocationWorldValidation := none, allocationParseBinding := none}}
  {p with program, lowering := none, rootSpanCache := none, tlsRows := none
          covarianceIndex := CompilerQueryIndices.covariance raw
          signatureAbiIndex := CompilerQueryIndices.signatureAbi p.runtime raw}
private def compare (p : CompilerProviders.Prepared) (span : Miri.MIR.SpanRef) : IO Unit := do
  let expected := CompilerValueConstants.callerLocationReference p span
  let actual := CompilerValueConstants.callerLocation p span
  unless decide (actual = expected) do throw (IO.userError s!"caller-location outcome differs at span{span.id}")

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected ordinary export fixture")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let program ← must (lowerCoreProgram decoded.document)
  let p := (← must (EvalPreparation.prepare program).outcome).compiler
  let records ← must ((← must (p.program.input.raw.getObjVal? "compiler_caller_location_constants")).getArr?)
  let some row := records[0]? | throw (IO.userError "fixture has no caller-location rows")
  let some storedSpan := p.program.compilerTables.spans[0]? | throw (IO.userError "fixture has no source spans")
  let spanJson ← must (Json.parse storedSpan.originalPayload)
  let row := set row "span" spanJson
  let span : Miri.MIR.SpanRef := ⟨0⟩
  unless (CompilerValueConstants.callerLocationReference (withRows p (.arr #[row])) span).isOk do
    throw (IO.userError "positive caller-location fixture did not decode")
  compare (withRows p (.arr #[row])) span
  compare (withRows p (.arr #[row,row])) span
  compare (withRows p (.arr #[row,set row "status" (.str "incomplete")])) span
  compare (withRows p (.arr #[row,Json.mkObj []])) span
  compare (withRows p (.arr #[Json.mkObj [],row])) span
  compare (withRows p (.arr #[])) span
  compare (withRows p (.str "not-an-array")) span
  -- Same coarse file/lo/hi key, distinct complete span: must not alias.
  let missing := set row "span" (set spanJson "ctxt" (.str "absent-context"))
  compare (withRows p (.arr #[missing,row])) span
  compare (withRows p (.arr #[row,missing])) span
  compare (withRows p (.arr #[Json.mkObj []])) ⟨p.program.compilerTables.spans.size⟩
  let literal ← must (CompilerValueConstants.callerLocation (withRows p (.arr #[row])) span)
  let legacyTemplate ← must (CompilerValueConstants.callerLocationTemplate (withRows p (.arr #[row])) span)
  unless decide (legacyTemplate = (literal.1,literal.2,none)) do
    throw (IO.userError "legacy caller-location template changed its literal")
  let recipe := set (set (set (set row "recipe_schema" (.str "caller_location_template_v1"))
    "template_value" (← must (row.getObjVal? "value"))) "line_u32" (toJson (2^32-1 : Nat)))
    "column_u32" (toJson (0 : Nat))
  let actual ← must (CompilerValueConstants.callerLocationTemplate (withRows p (.arr #[recipe])) span)
  unless decide (actual = (literal.1,literal.2,some (2^32-1,0))) do
    throw (IO.userError "recipe template or u32 coordinates changed")
  unless !(CompilerValueConstants.callerLocation (withRows p (.arr #[recipe])) span).isOk do
    throw (IO.userError "literal API returned an uninstantiated recipe")
  for bad in [set recipe "line_u32" (toJson (2^32 : Nat)),
      set recipe "column_u32" (toJson (2^32 : Nat)),
      set recipe "recipe_schema" (.str "future"),
      set recipe "template_value" .null,
      set recipe "status" (.str "unsupported")] do
    unless !(CompilerValueConstants.callerLocationTemplate (withRows p (.arr #[bad])) span).isOk do
      throw (IO.userError "malformed caller-location recipe accepted")
  IO.println "caller-location reference/indexed success, duplicates, errors, collisions and base isolation: PASS"
