import MiriTests.Input.ReferenceDecoder
import Miri.Input.CompilerConstantQueries
import Miri.Input.CompilerLifecycle
import Miri.Input.Reader.BodyMetadata

/-! Compare production and comparison-oracle imports on the same shared graph.
Failed constant and required-constant batches are tested at the reader boundary,
where their table changes now occur. -/
open Lean Miri.Input Miri.Interpreter

private def must (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def arrayEqual (left right : Array α) (equal : α → α → Bool) : Bool :=
  left.size == right.size && (left.toList.zip right.toList).all fun (a,b) => equal a b

private def resultEqual : Except String Miri.Interpreter.CompilerConstantEvidence →
    Except String Miri.Interpreter.CompilerConstantEvidence → Bool
  | .error a,.error b => a == b
  | .ok a,.ok b => a.fnInstance == b.fnInstance && a.original == b.original &&
      a.normalized == b.normalized && a.span == b.span && a.value == b.value
  | _,_ => false

private def evidenceEqual (left right : CompilerConstantQueries.Prepared) : Bool :=
  arrayEqual left.bodies right.bodies fun left right =>
    match left,right with
    | .error a,.error b => a == b
    | .ok a,.ok b => arrayEqual a b fun left right =>
      match left,right with
      | none,none => true
      | some a,some b => resultEqual a b
      | _,_ => false
    | _,_ => false

private def lifecycleSignature (prepared : CompilerLifecycle.Prepared) :=
  prepared.entries.map fun entry => reprStr
    (entry.preamble,entry.callee,entry.checks.map fun checks => checks.map fun result =>
      result.map fun value => (value.fnInstance,value.original,value.normalized,value.span,value.value))

private def constantCount (prepared : CompilerConstantQueries.Prepared) : Nat :=
  prepared.bodies.foldl (fun count body => count +
    (body.toOption.map fun table => (table.filterMap fun entry => entry.bind Except.toOption).size).getD 0) 0

private def setField (value : Json) (key : String) (replacement : Json) : Json :=
  match value with
  | .obj fields => Json.mkObj ((key,replacement) :: fields.toList.filter (·.1 != key))
  | _ => value

private def span : Json :=
  let position := Json.mkObj [("line",toJson (1 : Nat)),("column",toJson (1 : Nat))]
  let diagnostic := Json.mkObj [("status",toJson "debug_payload"),("rustc_debug",toJson "rollback")]
  Json.mkObj [("lo",toJson (987654321 : Nat)),("hi",toJson (987654322 : Nat)),
    ("start",position),("end",position),("ctxt",diagnostic),("file",diagnostic)]

private def operand : Json := Json.mkObj [("status",toJson "supported"),
  ("type",Json.mkObj [("type_id",toJson (0 : Nat))]),("user_type_annotation",.null),("span",span),
  ("constant",Json.mkObj [("status",toJson "supported"),("value",Json.mkObj [("kind",toJson "zero_sized")]),
    ("source",Json.mkObj [("kind",toJson "already_evaluated")])])]

private def catalog (value : Json) : Except String Reader.Catalog :=
  Reader.Catalog.parse (Json.mkObj [("shared_payloads",Json.mkObj [
    ("schema_version",toJson (2 : Nat)),("nodes",Json.arr #[])]),("body",value)])

private def body (checks : Array Json) : Json :=
  Json.mkObj [("source_scopes",Json.arr #[]),("basic_blocks",Json.arr #[]),("backtrace_spans",Json.arr #[]),
    ("required_consts",Json.arr (checks.map fun _ => operand)),
    ("constant_query_context",Json.mkObj [
      ("instance_kind",Json.mkObj [("kind",toJson "item"),("def_id",Json.mkObj [
        ("crate",toJson (0 : Nat)),("index",toJson (0 : Nat))])]),("generic_args",Json.arr #[]),
      ("required_constant_checks",Json.mkObj [("status",toJson "supported"),
        ("typing_env",toJson "body_typing_env"),("checks",Json.arr checks)])])]

private def check (index : Nat) (result : Json) : Json :=
  Json.mkObj [("index",toJson index),("span",span),("result",result)]

private def readerChecks : IO Unit := do
  let ctx : Reader.ConstantReader.Context := ⟨1,0,#[some 0]⟩
  let initial := Reader.MIRReader.initial 0 {definitions := #[⟨0,0⟩]}
  let failedOperand := setField operand "constant" (Json.mkObj [
    ("status",toJson "unsupported"),("source",Json.mkObj [("kind",toJson "already_evaluated")])])
  let source ← must (catalog failedOperand)
  let attempt : Reader.MIRReader.Decode (Except String Nat) := do
    try pure (.ok (← Reader.ConstantReader.constant source ctx failedOperand "constant"))
    catch reason => pure (.error reason)
  let (failed,after) ← must (attempt.run initial)
  unless failed.toOption.isNone && after.compiler == initial.compiler &&
      after.tables.constants == initial.tables.constants do
    throw (IO.userError "failed constant reader retained a span or constant appended before failure")

  let failedEvaluation := Json.mkObj [("status",toJson "supported"),("normalized_operand",operand),
    ("value",Json.mkObj [("kind",toJson "invalid_evaluation_kind")])]
  let input := body #[check 0 failedEvaluation]
  let source ← must (catalog input)
  let (metadata,after) ← must ((Reader.BodyMetadataReader.read source ctx input "body").run initial)
  unless metadata.callee.isOk && metadata.requiredConstants.toOption.isNone &&
      after.compiler == initial.compiler && after.tables.constants == initial.tables.constants do
    throw (IO.userError "failed required-constant batch retained pre-failure table additions")

  let failure := Json.mkObj [("kind",toJson "required_const_evaluation_error")]
  let unresolved := Json.mkObj [("kind",toJson "unresolved")]
  let input := body #[check 0 failure,check 1 unresolved]
  let source ← must (catalog input)
  let (metadata,_) ← must ((Reader.BodyMetadataReader.read source ctx input "body").run initial)
  let outcomes ← must metadata.requiredConstants
  match outcomes.toList with
  | [.error (.invalidProgram _),.error (.unsupported _)] => pure ()
  | _ => throw (IO.userError "required-constant source order or failure classification changed")
  let input := body #[check 1 failure]
  let source ← must (catalog input)
  let (metadata,after) ← must ((Reader.BodyMetadataReader.read source ctx input "body").run initial)
  unless metadata.requiredConstants == .error "required-constant source order mismatch" &&
      after.compiler == initial.compiler && after.tables.constants == initial.tables.constants do
    throw (IO.userError "out-of-order required-constant batch was accepted or changed tables")
  let context ← must (input.getObjVal? "constant_query_context")
  let malformed := setField input "constant_query_context" (setField context "instance_kind"
    (Json.mkObj [("kind",toJson "invalid_compiler_instance_kind")]))
  let source ← must (catalog malformed)
  let (metadata,after) ← must ((Reader.BodyMetadataReader.read source ctx malformed "body").run initial)
  unless metadata.callee.toOption.isNone && after.compiler == initial.compiler do
    throw (IO.userError "malformed current-instance query was accepted or changed definitions")

def main (args : List String) : IO Unit := do
  readerChecks
  let [path] := args | throw (IO.userError "expected shared-graph exporter JSON path")
  let text ← IO.FS.readFile path
  let production ← must (decodeRuntimeJson text)
  let reference ← must (decodeRuntimeJsonReference text)
  let program ← must (lowerCoreProgram production.document)
  let comparison ← must (lowerCoreProgram reference.document)
  let prepared ← must (CompilerConstantQueries.prepare (← must (RuntimeProgram.ofProgram program)))
  let expected ← must (CompilerConstantQueries.prepare (← must (RuntimeProgram.ofProgram comparison)))
  unless program.input.mirTables.mir == comparison.input.mirTables.mir &&
      program.compilerTables == comparison.compilerTables &&
      evidenceEqual prepared expected && prepared.obligations == expected.obligations do
    throw (IO.userError "shared-graph constant preparation differs from comparison-oracle import")
  unless constantCount prepared > 0 do throw (IO.userError "fixture contains no normalized constant query")
  let lifecycle := CompilerLifecycle.prepare program
  let expectedLifecycle := CompilerLifecycle.prepare comparison
  unless lifecycle.program.compilerTables == expectedLifecycle.program.compilerTables &&
      lifecycleSignature lifecycle == lifecycleSignature expectedLifecycle do
    throw (IO.userError "shared-graph lifecycle preparation differs from comparison-oracle import")
  IO.println s!"typed constant/lifecycle preparation and reader rollback/order: PASS ({constantCount prepared} constants)"
