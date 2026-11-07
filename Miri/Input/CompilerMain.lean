import Miri.Input.RuntimeProgram
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
  owner : RuntimeProgram
  start : Option MIR.DefId
  compilerEntry : Option MIR.DefId
  /-- Exact rustc EntryFnType attached to tcx.entry_fn. When absent, the
  compiler did not select a Rust main and the source may use Miri's
  separately selected miri_start entry. -/
  compilerEntryType : Except String (Option (MIR.DefId × MainEntryType))
  entries : Array Entry
  sections : Except String (Array SectionQuery)
@[inline] def Prepared.program (prepared : Prepared) : LoweredProgram := prepared.owner.program
@[inline] def Prepared.runtime (prepared : Prepared) : RuntimeMetadata := prepared.owner.runtime

def Prepared.withProgram (prepared : Prepared) (program : LoweredProgram) : Prepared :=
  {prepared with owner := prepared.owner.withProgram program}

def prepare (owner : RuntimeProgram) : Except String Prepared := do
  let program := owner.program
  let runtime := owner.runtime
  let source ← program.input.mirTables.mainQueries
  let entries := source.entries.map fun entry =>
    let parameters := entry.parameters.map fun parameter =>
      match parameter with
      | .lifetime => MainGenericParameter.lifetime
      | .typeParameter => .typeParameter
      | .constParameter => .constParameter
    let signature := entry.signature.map fun value =>
      (⟨value.hasBoundVariables,value.outputHasBoundVariables,value.returnType,value.fnPointerType⟩ : MainSignature)
    (⟨entry.definition,parameters,signature,entry.start⟩ : Entry)
  let sections := source.sections.map fun entries => entries.map fun entry =>
    (⟨entry.name,entry.result.map fun value => (⟨value.definition,value.span,value.ty,value.allocation⟩ : Section)⟩ : SectionQuery)
  let entryType := source.compilerEntryType.map fun value => value.map fun (definition,sigpipe) =>
    (definition,MainEntryType.rustcMain sigpipe)
  return ⟨owner,source.start,source.compilerEntry,entryType,entries,sections⟩
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
    cNoUnwind := .C false
    genericParameters := fun id => lift do return (← entry p id).parameters
    entrySignature := fun id => lift do (← entry p id).signature
    startLangItem := pure p.start
    resolveInstance := fun id args => lift (resolve p id args)
    layoutOf := fun ty => lift (p.runtime.lookup ty |>.mapError toString)}
end Miri.Input.CompilerMain
