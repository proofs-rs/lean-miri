import Miri.Input.CompilerInstance
import Miri.Interpreter.Panic

/-! Exact language-item definitions and Instance::mono generic parameters.
Definition IDs are appended before shared provider preparation. Missing query
metadata stays a demanded compiler obligation, never a successful panic. -/
namespace Miri.Input.CompilerPanicFacts
open Lean Miri.ABI Miri.Interpreter

def name : Panic.LangItem → String
  | .Panic => "Panic"
  | .PanicNounwind => "PanicNounwind"
  | .PanicBoundsCheck => "PanicBoundsCheck"
  | .PanicMisalignedPointerDereference => "PanicMisalignedPointerDereference"
  | .PanicAddOverflow => "PanicAddOverflow"
  | .PanicSubOverflow => "PanicSubOverflow"
  | .PanicMulOverflow => "PanicMulOverflow"
  | .PanicDivOverflow => "PanicDivOverflow"
  | .PanicRemOverflow => "PanicRemOverflow"
  | .PanicNegOverflow => "PanicNegOverflow"
  | .PanicShrOverflow => "PanicShrOverflow"
  | .PanicShlOverflow => "PanicShlOverflow"
  | .PanicDivZero => "PanicDivZero"
  | .PanicRemZero => "PanicRemZero"
  | .PanicNullPointerDereference => "PanicNullPointerDereference"
  | .PanicNullReferenceConstructed => "PanicNullReferenceConstructed"
  | .PanicInvalidEnumConstruction => "PanicInvalidEnumConstruction"
  | .PanicCoroutineResumed => "PanicCoroutineResumed"
  | .PanicAsyncFnResumed => "PanicAsyncFnResumed"
  | .PanicAsyncGenFnResumed => "PanicAsyncGenFnResumed"
  | .PanicGenFnNone => "PanicGenFnNone"
  | .PanicCoroutineResumedPanic => "PanicCoroutineResumedPanic"
  | .PanicAsyncFnResumedPanic => "PanicAsyncFnResumedPanic"
  | .PanicAsyncGenFnResumedPanic => "PanicAsyncGenFnResumedPanic"
  | .PanicGenFnNonePanic => "PanicGenFnNonePanic"
  | .PanicCoroutineResumedDrop => "PanicCoroutineResumedDrop"
  | .PanicAsyncFnResumedDrop => "PanicAsyncFnResumedDrop"
  | .PanicAsyncGenFnResumedDrop => "PanicAsyncGenFnResumedDrop"
  | .PanicGenFnNoneDrop => "PanicGenFnNoneDrop"

private def parameterTag : MainGenericParameter → Nat
  | .lifetime => 0 | .typeParameter => 1 | .constParameter => 2

private def definition (program : LoweredProgram) (id : Nat) : Except String MIR.DefId := do
  unless id < program.compilerTables.definitions.size do throw "panic compiler definition ID out of bounds"
  pure id

private def rows (p : LoweredProgram) : Array Catalog.PanicQuery := p.input.queries.panic

def prepareProgram (program : LoweredProgram) : Except String LoweredProgram := do
  let mut tags : Array String := #[]
  for row in rows program do
    if tags.contains row.langItem then throw "duplicate panic language-item query"
    tags := tags.push row.langItem
    if let some id := row.definition then
      let _ ← definition program id
      pure ()
  pure program

def langItemByName (program : LoweredProgram) (tag : String) : Except String (Option MIR.DefId) := do
  let selected := (rows program).filter fun row => row.langItem == tag
  unless selected.size == 1 do throw "exact panic language-item query is missing or duplicated"
  let some row := selected[0]? | throw "panic language-item query absent"
  row.definition.mapM (definition program)

def langItem (program : LoweredProgram) (item : Panic.LangItem) : Except String (Option MIR.DefId) :=
  langItemByName program (name item)

def genericParameters (program : LoweredProgram) (requested : MIR.DefId) :
    Except String (Array MainGenericParameter) := do
  let mut found : Option (Array MainGenericParameter) := none
  for row in rows program do
    let some rawId := row.definition | continue
    let id ← definition program rawId
    unless id == requested do continue
    let some rawParams := row.genericParameters | throw "compiler panic generic parameters absent"
    let params ← rawParams.mapM fun value => do
      match value with
      | "lifetime" => pure MainGenericParameter.lifetime
      | "type_parameter" => pure .typeParameter
      | "const_parameter" => pure .constParameter
      | _ => throw "unknown compiler panic generic parameter kind"
    if let some earlier := found then
      unless earlier.map parameterTag == params.map parameterTag do throw "conflicting compiler generic parameters for panic definition"
    found := some params
  match found with
  | none => throw "compiler panic definition has no generic-parameter query"
  | some params => pure params
/-- machine.rs::unwind_terminate uses reason.lang_item followed by
Instance::mono, retaining erased lifetime arguments and rejecting type/const
parameters. Missing compiler records remain unsupported; absent required lang
items are source invariant errors. -/
def unwindTerminate (program : LoweredProgram) (reason : MIR.UnwindTerminateReason) :
    Except StepError CallInstance := do
  let tag := match reason with | .Abi => "PanicCannotUnwind" | .InCleanup => "PanicInCleanup"
  let some definition ← langItemByName program tag |>.mapError StepError.unsupported
    | throw (.invalidProgram "missing unwind termination language item")
  let mut args := #[]
  for parameter in ← genericParameters program definition |>.mapError StepError.unsupported do
    match parameter with
    | .lifetime => args := args.push (.Lifetime .Erased)
    | .typeParameter | .constParameter =>
      throw (.invalidProgram "Instance::mono called on type/const generic unwind termination item")
  CompilerInstance.item (LowerContext.ofDocument program.input) program.compilerTables definition args
    |>.mapError StepError.unsupported
end Miri.Input.CompilerPanicFacts
