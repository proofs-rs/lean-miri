import Miri.Input.CompilerInstance
import Miri.Input.CompilerExternAbi
import Miri.Interpreter.MainMachine

/-! eval.rs::call_main entry signature and lang_start queries. Original bound
variables, return type and Ty::new_fn_ptr identity are retained. Resolution is
keyed by the exact start DefId and complete source generic argument vector.
Link-section static reading remains a separate stateful global-memory query.
-/
namespace Miri.Input.CompilerMain
open Lean Miri.ABI Miri.Interpreter
structure Entry where
  definition : MIR.DefId
  parameters : Array MainGenericParameter
  signature : Except String MainSignature
  start : Except String (Option CallInstance)
structure Section where
  definition : MIR.DefId
  span : MIR.SpanRef
  ty : MIR.TyId
  allocation : AllocationId
structure SectionQuery where
  name : String
  result : Except String Section
structure Prepared where
  program : LoweredProgram
  runtime : RuntimeMetadata
  start : Option MIR.DefId
  compilerEntry : Option MIR.DefId
  /-- Exact rustc EntryFnType attached to tcx.entry_fn. When absent, the
  compiler did not select a Rust main and the source may use Miri's
  separately selected miri_start entry. -/
  compilerEntryType : Except String (Option (MIR.DefId × MainEntryType))
  entries : Array Entry
  sections : Except String (Array SectionQuery)
private def definition (tables : CompilerTables) (id : Nat) : Except String MIR.DefId := do
  unless id < tables.definitions.size do throw "compiler definition ID out of bounds"
  pure id

private def typeId (context : LowerContext) (id : Nat) : Except String MIR.TyId := do
  unless context.containsTypeId id do throw "main compiler query references missing type"
  pure id

def prepare (runtime : RuntimeMetadata) (program : LoweredProgram) : Except String Prepared := do
  let source := program.input.queries.main
  let ctx := LowerContext.ofDocument program.input
  let tables := program.compilerTables
  let start ← source.startLangItem.mapM (definition tables)
  let compilerEntry ← source.compilerEntry.mapM (definition tables)
  let compilerEntryType : Except String (Option (MIR.DefId × MainEntryType)) := do
    match source.compilerEntryType with
    | none =>
      if compilerEntry.isSome then throw "rustc selected main lacks exact EntryFnType query"
      pure none
    | some value =>
      let id ← definition tables value.definition
      unless compilerEntry == some id do throw "rustc EntryFnType definition differs from compiler-selected entry"
      unless value.kind == "rustc_main" do throw s!"unsupported rustc EntryFnType `{value.kind}`"
      unless value.sigpipe <= 255 do throw "rustc EntryFnType sigpipe does not fit u8"
      pure (some (id, .rustcMain (UInt8.ofNat value.sigpipe)))
  let mut entries : Array Entry := #[]
  for record in source.entries do
    let id ← definition tables record.definition
    if entries.any (·.definition == id) then throw "duplicate source main definition key"
    let parameters ← record.genericParameters.mapM fun value => do
      match value with
      | "lifetime" => pure MainGenericParameter.lifetime
      | "type_parameter" => pure .typeParameter | "const_parameter" => pure .constParameter
      | _ => throw "unknown main generic parameter kind"
    let signature := do
      pure (⟨record.signature.hasBoundVariables, record.signature.outputHasBoundVariables,
        ← typeId ctx record.signature.returnType,
        ← typeId ctx record.signature.functionPointerType⟩ : MainSignature)
    let outcome : Except String (Option CallInstance) := do
      unless record.signature.compilerSelectedEntry do
        throw "lang_start query not requested for a non-compiler-selected entry"
      record.signature.startResolution.mapM fun value => do
        let _ ← CompilerInstance.source ctx value.instanceId
        pure value.instanceId
    entries := entries.push ⟨id, parameters, signature, outcome⟩
  let sectionsResult : Except String (Array SectionQuery) := do
    let some records := source.linkSections | throw "compiler link-section catalog absent"
    records.mapM fun record => do
      let result := do
        let id ← definition tables record.definition
        unless record.span < tables.spans.size do throw "link-section span absent from compiler table"
        let ty ← typeId ctx record.typeId
        unless ctx.containsAllocationId record.allocation do throw "link-section static allocation missing from compiler graph"
        pure (⟨id, ⟨record.span⟩, ty, record.allocation⟩ : Section)
      pure ⟨record.sectionName, result⟩
  pure ⟨program, runtime, start, compilerEntry, compilerEntryType, entries, sectionsResult⟩
private def entry (p : Prepared) (definition : MIR.DefId) : Except String Entry := do
  let some entry := p.entries.find? (·.definition == definition) | throw "missing exact source main entry query"
  pure entry

def resolve (p : Prepared) (definition : MIR.DefId) (args : Array MIR.GenericArg) : Except String (Option CallInstance) := do
  unless p.start == some definition do throw "main resolution request is not the actual start lang item"
  let some entryId := p.compilerEntry | throw "source compiler has no executable entry"
  let entry ← entry p entryId
  let signature ← entry.signature
  unless args == #[.Type signature.returnType] do throw "missing exact lang_start argument-vector query"
  entry.start

/-- Exact compiler-selected ordinary entry metadata for the source startup
factory. `none` is retained for the separate MiriStart entry path. -/
def sourceCompilerEntry (p : Prepared) : Except String (Option (MIR.DefId × MainEntryType)) :=
  p.compilerEntryType

private def lift (value : Except String A) : MainMachine.M U A :=
  match value with | .ok value => pure value | .error error => throw (.unsupported error)

def hooks (p : Prepared) (base : MainMachine.Hooks U C O ABI.ExternAbi F A Aff P) :
    MainMachine.Hooks U C O ABI.ExternAbi F A Aff P :=
  {base with
    itemInstance := fun definition args => lift (CompilerInstance.item (LowerContext.ofDocument p.program.input) p.program.compilerTables definition args)
    cNoUnwind := .C false
    genericParameters := fun id => lift do return (← entry p id).parameters
    entrySignature := fun id => lift do (← entry p id).signature
    startLangItem := pure p.start
    resolveInstance := fun id args => lift (resolve p id args)
    layoutOf := fun ty => lift (p.runtime.lookup ty |>.mapError toString)}
end Miri.Input.CompilerMain
