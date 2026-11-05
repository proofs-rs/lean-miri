import Miri.Input.CompilerGlobals
import Miri.Interpreter.ThreadLocal

/-! Source: Miri concurrency/thread.rs::get_or_create_thread_local_alloc;
rustc GlobalAlloc static queries and eval_static_initializer. Exported TLS
initializers are compiler results; each runtime thread receives a fresh mutable
copy via the source allocation-adjustment pipeline. -/
namespace Miri.Input.CompilerThreadLocal
open Lean Miri.ABI Miri.Memory Miri.Interpreter

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def natField (j : Json) (key : String) : Except String Nat := do (← field j key).getNat?
private def stringField (j : Json) (key : String) : Except String String := do (← field j key).getStr?

private partial def collectInto (j : Json) (found : Array Json) : Array Json :=
  let found := if (DecoderValues.optionalStringValue j "kind") == some "ThreadLocalRef" then found.push j else found
  match j with
  | .arr values => values.foldl (fun found value => collectInto value found) found
  | .obj values => values.foldl (fun found _ value => collectInto value found) found
  | _ => found

private def collect (j : Json) : Array Json := collectInto j #[]

/-- Preserve the exact ordered scan, including duplicate and malformed rows. -/
structure Rows (raw : Json) where
  private mk ::
  values : Array Json
  private exact : values = collect raw

def Rows.prepare (raw : Json) : Rows raw := ⟨collect raw, rfl⟩

theorem Rows.values_eq {raw : Json} (rows : Rows raw) : rows.values = collect raw := rows.exact

structure Entry where
  definition : MIR.DefId
  info : StaticGlobalInfo
  initializer : Option AllocationMemory
  payload : Json

/-- Missing, failed and foreign initializer queries remain explicit failures;
no TLS identity is obtained by interpreting diagnostic names. -/
def ofProgram (program : LoweredProgram)
    (preparedRows : Option (Rows program.input.raw) := none) : Except String (Array Entry) := do
  let mut entries := #[]
  let values := match preparedRows with
    | some rows => rows.values
    | none => collect program.input.raw
  for value in values do
    let defJson ← field value "def_id"
    let sourceId : DefinitionId := ⟨← natField defJson "crate", ← natField defJson "index"⟩
    let definition ← lookupDefinitionId program.bundle.definitions sourceId
    let info ← decodeStaticGlobalInfo (← field value "global_info")
    unless info.status == .supported && info.isStatic && info.threadLocal do
      throw "TLS declaration compiler query evidence is unresolved or inconsistent"
    let initializer ← field value "initializer"
    let memory ← if info.foreignItem then pure none else do
      unless (← stringField initializer "status") == "supported" do throw "TLS initializer query failed"
      pure (some (← decodeAllocationMemoryEvidence (← field initializer "allocation")))
    if let some previous := entries.find? (fun entry => entry.definition == definition) then
      unless (previous.payload.getObjVal? "initializer").toOption == some initializer && previous.info.payload == info.payload do
        throw "conflicting compiler TLS query evidence"
    else entries := entries.push ⟨definition, info, memory, value⟩
  pure entries

/-- Caching preserves duplicate checks, diagnostics and result order. -/
theorem ofProgram_preparedRows (program : LoweredProgram) (rows : Rows program.input.raw) :
    ofProgram program (some rows) = ofProgram program := by
  simp only [ofProgram, Rows.values_eq]

private def find (entries : Array Entry) (definition : MIR.DefId) : Except String Entry :=
  match entries.find? (·.definition == definition) with
  | some entry => pure entry
  | none => throw "missing compiler TLS declaration/initializer evidence"

/-- Select this exact compiler definition before decoding any initializer.
Other TLS declarations, including unsupported initializers, are not demanded
by this source lookup. The canonical definition table is unchanged. -/
def forDefinition (program : LoweredProgram) (definition : MIR.DefId)
    (preparedRows : Option (Rows program.input.raw) := none) : Except String Entry := do
  let some target := program.bundle.definitions[definition]?
    | throw "TLS definition absent from canonical compiler table"
  let values := match preparedRows with
    | some rows => rows.values
    | none => collect program.input.raw
  let rows := values.filter fun value =>
    let actual := do
      let raw ← field value "def_id"
      pure (⟨← natField raw "crate", ← natField raw "index"⟩ : DefinitionId)
    actual.toOption == some target
  unless !rows.isEmpty do throw "missing exact compiler TLS declaration/initializer evidence"
  -- Reuse the existing strict decoder on the selected records with the same
  -- source tables; this is a query view, never a second program representation.
  let selected := {program with input := {program.input with raw := .arr rows, allocationWorldValidation := none, allocationParseBinding := none, rawReflexivity := none}}
  find (← ofProgram selected) definition

theorem forDefinition_preparedRows (program : LoweredProgram) (definition : MIR.DefId)
    (rows : Rows program.input.raw) :
    forDefinition program definition (some rows) = forDefinition program definition := by
  rcases rows with ⟨values, exact⟩
  cases exact
  rfl

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
