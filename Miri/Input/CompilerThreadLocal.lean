import Miri.Input.CompilerGlobals
import Miri.Interpreter.ThreadLocal

/-! Source: Miri concurrency/thread.rs::get_or_create_thread_local_alloc;
rustc GlobalAlloc static queries and eval_static_initializer. Exported TLS
initializers are compiler results; each runtime thread receives a fresh mutable
copy via the source allocation-adjustment pipeline. -/
namespace Miri.Input.CompilerThreadLocal
open Lean Miri.ABI Miri.Memory Miri.Interpreter

abbrev Entry := ThreadLocalQueryData

/-- Checked typed source records, prepared once while reading MIR. -/
def ofProgram (program : LoweredProgram) : Except String (Array Entry) := do
  let entries ← program.input.mirTables.threadLocals.all
  for entry in entries do
    let some source := program.bundle.definitions[entry.definition]? |
      throw "TLS definition absent from canonical compiler table"
    unless source == entry.sourceDefinition do throw "TLS compiler definition table identity mismatch"
  return entries

private def find (entries : Array Entry) (definition : MIR.DefId) : Except String Entry :=
  match entries.find? (·.definition == definition) with
  | some entry => pure entry
  | none => throw "missing compiler TLS declaration/initializer evidence"

/-- Select this exact compiler definition before decoding any initializer.
Other TLS declarations, including unsupported initializers, are not demanded
by this source lookup. The canonical definition table is unchanged. -/
def forDefinition (program : LoweredProgram) (definition : MIR.DefId) : Except String Entry := do
  let some target := program.bundle.definitions[definition]? |
    throw "TLS definition absent from canonical compiler table"
  let result ← program.input.mirTables.threadLocals.entries.lookup definition |>.mapError
    (fun _ => "missing exact compiler TLS declaration/initializer evidence")
  let entry ← result
  unless entry.sourceDefinition == target do throw "TLS compiler definition table identity mismatch"
  return entry

/-- Machine leaves supply byte storage, provenance adjustment and allocation
hooks. Compiler leaves are replaced by checked evidence keyed by shared DefId.
The source runtime cache is checked before any of these query leaves are used. -/
def queries (target : RuntimeTargetDataLayout) (entries : Array Entry)
    (machine : ThreadLocalQueries P E H Params) : ThreadLocalQueries P E H Params :=
  { machine with
    isForeignItem := fun definition => do
      let entry ← match find entries definition with
        | .ok entry => pure entry
        | .error error => throw (.query error)
      pure entry.info.foreignItem
    evaluateStaticInitializer := fun definition => do
      let entry ← match find entries definition with
        | .ok entry => pure entry
        | .error error => throw (.query error)
      let some initializer := entry.initializer | throw (.query "compiler TLS initializer is unavailable")
      let state ← EStateM.get
      match AllocationImage.decode target state.memory initializer with
      | .ok allocation => pure allocation
      | .error error => throw (.query error) }

end Miri.Input.CompilerThreadLocal
