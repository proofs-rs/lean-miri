import Miri.Input.CompilerGlobals
import Miri.Interpreter.ThreadLocal

/-! Source: Miri concurrency/thread.rs::get_or_create_thread_local_alloc;
rustc GlobalAlloc static queries and eval_static_initializer. Exported TLS
initializers are compiler results; each runtime thread receives a fresh mutable
copy via the source allocation-adjustment pipeline. -/
namespace Miri.Input.CompilerThreadLocal
open Lean Miri.ABI Miri.Memory Miri.Interpreter

structure Entry where
  definition : MIR.DefId
  info : StaticGlobalInfo
  initializer : Option AllocationMemory

private def ofRows (program : LoweredProgram) (rows : Array ThreadLocalEvidence) : Except String (Array Entry) := do
  let mut entries := #[]
  for value in rows do
    let definition := value.definition
    unless definition < program.bundle.definitions.size do throw "TLS compiler definition ID out of bounds"
    unless value.info.isStatic && value.info.threadLocal do
      throw "TLS declaration compiler query evidence is unresolved or inconsistent"
    if let some previous := entries.find? (fun entry => entry.definition == definition) then
      unless previous.initializer == value.initializer && previous.info == value.info do
        throw "conflicting compiler TLS query evidence"
    else entries := entries.push ⟨definition, value.info, value.initializer⟩
  pure entries

def ofProgram (program : LoweredProgram) : Except String (Array Entry) :=
  ofRows program ((program.input.bodies.map fun body => body.toBodyCore.threadLocals).flatten)

private def find (entries : Array Entry) (definition : MIR.DefId) : Except String Entry :=
  match entries.find? (·.definition == definition) with
  | some entry => pure entry
  | none => throw "missing compiler TLS declaration/initializer evidence"

def forDefinition (program : LoweredProgram) (definition : MIR.DefId) : Except String Entry := do
  let some _ := program.bundle.definitions[definition]?
    | throw "TLS definition absent from canonical compiler table"
  let rows := ((program.input.bodies.map fun body => body.toBodyCore.threadLocals).flatten).filter
    (·.definition == definition)
  unless !rows.isEmpty do throw "missing exact compiler TLS declaration/initializer evidence"
  find (← ofRows program rows) definition

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
