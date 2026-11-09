import Miri.Input.CompilerLinkSections

/-! helpers.rs::eval_path and eval_context.rs::eval_global for exact named
libc globals used by pthread synchronization. Query identity is the full source
path; static and const allocations are materialized through the canonical
allocation image and root-pointer operations. -/
namespace Miri.Input.CompilerNamedGlobals
open Lean Miri.ABI Miri.Memory Miri.Interpreter

structure Value where
  definition : MIR.DefId
  ty : MIR.TyId
  allocation : AllocationId
  isStatic : Bool

structure Entry where
  name : String
  result : Value

structure Prepared where
  program : LoweredProgram
  runtime : RuntimeMetadata
  entries : Array Entry

def prepare (runtime : RuntimeMetadata) (program : LoweredProgram) : Except String Prepared := do
  let ctx := LowerContext.ofDocument program.input
  let mut entries := #[]
  for record in program.input.queries.namedStatics.getD #[] do
    let name := record.name
    unless record.path == #["libc", name] do throw "named compiler global path must be exactly libc::<name>"
    unless !(entries.any (·.name == name)) do throw "duplicate compiler named global query"
    unless record.definition < program.compilerTables.definitions.size do throw "compiler definition ID out of bounds"
    unless ctx.containsTypeId record.typeId do throw "named compiler global references absent compiler type"
    unless ctx.containsAllocationId record.allocation do throw "named compiler global references absent allocation image"
    let result : Value := ⟨record.definition, record.typeId, record.allocation, record.isStatic⟩
    entries := entries.push ⟨name, result⟩
  pure ⟨program, runtime, entries⟩

private def value (prepared : Prepared) (name : String) : Except String Value := do
  let some entry := prepared.entries.find? (·.name == name)
    | throw s!"missing exact compiler named global query libc::{name}"
  pure entry.result

private def lift (query : Except String A) : MachineHooks.M K U A :=
  match query with
  | .ok value => pure value
  | .error reason => throw (.unsupported reason)

/-- Execute the source global-root-pointer query using the imported compiler
allocation and ordinary extern/static pointer hooks. No name or byte-content
lookup substitutes for the exact compiler row. -/
def global (prepared : Prepared) (memory : CompilerLinkSections.Memory K U Other)
    (name : String) : MachineHooks.M K U (MPlaceTy Provenance) := do
  let entry ← lift (value prepared name)
  let operand ← CompilerLinkSections.globalRef prepared.runtime memory
    ⟨entry.definition, entry.ty, entry.allocation, entry.isStatic⟩
  match operand.op with
  | .indirect place => pure ⟨place, operand.layout⟩
  | .immediate _ => throw (.invalidProgram "source eval_global named initializer did not produce an indirect place")

end Miri.Input.CompilerNamedGlobals
