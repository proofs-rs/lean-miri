import Miri.Input.EvalPreparation
import Miri.Input.CompilerValueConstants
import Miri.Input.Reader.ValueConstants

open Lean Miri.Input Miri.Interpreter

private def must (value : Except String α) : IO α :=
  match value with | .ok x => pure x | .error e => throw (IO.userError e)
private def set (j : Json) (key : String) (value : Json) : Json :=
  match j with
  | .obj fields => Json.mkObj ((key,value) :: fields.toList.filter (fun e => e.1 != key))
  | _ => Json.mkObj [(key,value)]
private def spanJson (span : SourceSpanData) : Json :=
  let position := fun value => Json.mkObj [("line", toJson value.line), ("column", toJson value.column)]
  let diagnostic := fun value => Json.mkObj [("status", .str "debug_payload"), ("rustc_debug", .str value)]
  Json.mkObj [("lo", toJson span.lo), ("hi", toJson span.hi),
    ("start", position span.start), ("end", position span.end),
    ("ctxt", diagnostic span.context), ("file", diagnostic span.file)]

private def withRows (p : CompilerProviders.Prepared) (rows : Json) : CompilerProviders.Prepared :=
  let input := Json.mkObj [("shared_payloads",Json.mkObj [("schema_version",toJson (2 : Nat)),
    ("nodes",Json.arr p.program.input.sharedNodes)]),("compiler_caller_location_constants",rows)]
  let ctx := LowerContext.ofDocument p.program.input
  let result := do
    let catalog ← Reader.Catalog.parse input
    Reader.ValueConstantReader.callerLocations catalog
      ⟨ctx.typeIds.size,ctx.allocationIds.size,ctx.scalarSizes⟩
  let tables := {p.program.input.mirTables with callerLocationConstants := result}
  let owner := {p.owner with input := {p.owner.input with mirTables := tables}}
  {p with
    owner := owner
    covarianceIndex := CompilerQueryIndices.covariance owner.input.covarianceQueries
    signatureAbiIndex := CompilerQueryIndices.signatureAbi owner.runtime}

private def check (p : CompilerProviders.Prepared) (span : Miri.MIR.SpanRef) (success : Bool) : IO Unit := do
  let actual := CompilerValueConstants.callerLocation p span
  unless actual.isOk == success do throw (IO.userError s!"caller-location outcome differs at span{span.id}: {reprStr actual}")

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected ordinary export fixture")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let program ← must (lowerCoreProgram decoded.document)
  let p := (← must (EvalPreparation.prepare program).outcome).compiler
  let catalog ← must (Reader.Catalog.parse (← must (Json.parse (← IO.FS.readFile path))))
  let records ← must (catalog.array (← must (catalog.field catalog.root "compiler_caller_location_constants" "$")) "rows")
  let some row := records[0]? | throw (IO.userError "fixture has no caller-location rows")
  let row ← must (catalog.inspect row "row")
  let some storedSpan := p.program.compilerTables.spans[0]? | throw (IO.userError "fixture has no source spans")
  let spanJson := spanJson storedSpan
  let row := set row "span" spanJson
  let span : Miri.MIR.SpanRef := ⟨0⟩
  unless (CompilerValueConstants.callerLocation (withRows p (.arr #[row])) span).isOk do
    throw (IO.userError "positive caller-location fixture did not decode")
  check (withRows p (.arr #[row])) span true
  check (withRows p (.arr #[row,row])) span true
  check (withRows p (.arr #[row,set row "debug_only" (toJson "different payload")])) span true
  let value ← must (catalog.inspect (← must (catalog.field row "value" "row")) "value")
  let kind ← must (catalog.string (← must (catalog.field value "kind" "value")) "value")
  let differentValue ← match kind with
    | "pointer_scalar" | "indirect_allocation" => do
      let offset ← must (catalog.natural (← must (catalog.field value "offset_bytes" "value")) "value")
      pure (set value "offset_bytes" (toJson (offset + 1)))
    | "slice_allocation" => do
      let length ← must (catalog.natural (← must (catalog.field value "metadata_length" "value")) "value")
      pure (set value "metadata_length" (toJson (length + 1)))
    | "scalar" => do
      let bits ← must (catalog.string (← must (catalog.field value "bits_unsigned" "value")) "value")
      pure (set value "bits_unsigned" (toJson (if bits == "0" then "1" else "0")))
    | "pointer_scalar_without_provenance" => do
      let address ← must (catalog.string (← must (catalog.field value "address" "value")) "value")
      pure (set value "address" (toJson (if address == "0" then "1" else "0")))
    | "zero_sized" => pure (Json.mkObj [("kind",toJson "pointer_scalar_without_provenance"),
        ("address",toJson "1"),("address_width_bytes",toJson (8 : Nat))])
    | _ => throw (IO.userError "fixture has an unknown caller-location ConstValue")
  check (withRows p (.arr #[row,set row "value" differentValue])) span false
  let resultType ← must (catalog.natural (← must (catalog.field (← must (catalog.field row "result_type" "row")) "type_id" "row")) "row")
  let otherType := if resultType == 0 then 1 else 0
  check (withRows p (.arr #[row,set row "result_type" (Json.mkObj [("type_id",toJson otherType)])])) span false
  check (withRows p (.arr #[row,set row "status" (.str "incomplete")])) span false
  check (withRows p (.arr #[row,Json.mkObj []])) span false
  check (withRows p (.arr #[Json.mkObj [],row])) span false
  check (withRows p (.arr #[])) span false
  check (withRows p (.str "not-an-array")) span false
  -- Same coarse file/lo/hi key, distinct complete span: must not alias.
  let otherSpan := set spanJson "ctxt" (Json.mkObj [("status",toJson "debug_payload"),
    ("rustc_debug",toJson "another valid hygiene context")])
  let otherRow := set row "span" otherSpan
  check (withRows p (.arr #[otherRow])) span false
  check (withRows p (.arr #[otherRow,row])) span true
  check (withRows p (.arr #[row,otherRow])) span true
  let missing := set row "span" (set spanJson "ctxt" (.str "absent-context"))
  check (withRows p (.arr #[missing,row])) span false
  check (withRows p (.arr #[row,missing])) span false
  check (withRows p (.arr #[Json.mkObj []])) ⟨p.program.compilerTables.spans.size⟩ false
  IO.println "caller-location typed semantic duplicates, value/type conflicts, errors and span collisions: PASS"
