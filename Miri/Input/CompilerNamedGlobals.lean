import Miri.Input.RuntimeProgram
import Miri.Input.CompilerLinkSections

/-! helpers.rs::eval_path and eval_context.rs::eval_global for exact named
libc globals used by pthread synchronization. Query identity is the full source
path; static and const allocations are materialized through the canonical
allocation image and root-pointer operations. -/
namespace Miri.Input.CompilerNamedGlobals
open Lean Miri.ABI Miri.Memory Miri.Interpreter

abbrev Value := NamedGlobalValueData
abbrev Entry := NamedGlobalQueryData

structure Prepared where
  owner : RuntimeProgram
  entries : Array Entry

/-- Retain every exact path query, including unavailable rows. Failed queries
are raised only when the corresponding source path is demanded. -/
@[inline] def Prepared.program (prepared : Prepared) : LoweredProgram := prepared.owner.program
@[inline] def Prepared.runtime (prepared : Prepared) : RuntimeMetadata := prepared.owner.runtime

def Prepared.withProgram (prepared : Prepared) (program : LoweredProgram) : Prepared :=
  {prepared with owner := prepared.owner.withProgram program}

def prepare (owner : RuntimeProgram) : Except String Prepared := do
  let program := owner.program
  let runtime := owner.runtime
  let entries ← program.input.mirTables.namedGlobals
  pure ⟨owner, entries⟩

private def value (prepared : Prepared) (name : String) : Except String Value := do
  let some entry := prepared.entries.find? (·.name == name)
    | throw s!"missing exact compiler named global query libc::{name}"
  entry.result

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
