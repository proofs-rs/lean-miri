import Miri.Input.CompilerVirtualFacts
import Miri.Input.CompilerInstance

/-! Actual imported GlobalAlloc::Function/VTable identity leaves. Runtime
allocation IDs are resolved through AllocationImage's mapping, never equated
with exported IDs. Complete instances share the program's compiler tables. -/
namespace Miri.Input.CompilerVTableRuntime
open Lean Miri.Memory Miri.Interpreter
abbrev Result := Except String

structure Prepared where
  facts : CompilerFactAdapters.Prepared
  obligations : Array Obligation

def prepare (facts : CompilerFactAdapters.Prepared) : Prepared := Id.run do
  let mut obligations := #[]
  for (outcome,id) in facts.context.program.input.mirTables.instances.toList.zipIdx do
    if let .error error := outcome then
      obligations := obligations.push ⟨s!"instances[{id}].vtable_runtime",error⟩
  return ⟨facts,obligations⟩

structure GlobalLookup (prepared : Prepared) where
  private mk ::
  private definitionRows : Array DefinitionId
  private definitionIndex : Std.HashMap (Nat × Nat) Nat
  private exactDefinitions : definitionRows = prepared.facts.context.program.compilerTables.definitions

def GlobalLookup.prepare (prepared : Prepared) : GlobalLookup prepared := Id.run do
  let definitionRows := prepared.facts.context.program.compilerTables.definitions
  let mut definitionIndex : Std.HashMap (Nat × Nat) Nat := {}
  for (definition, index) in definitionRows.toList.zipIdx do
    let key := (definition.crateIndex, definition.index)
    if !(definitionIndex.contains key) then
      definitionIndex := definitionIndex.insert key index
  return ⟨definitionRows,definitionIndex,rfl⟩

def functionInstance (prepared : Prepared) (id : InstanceId) : Result CallInstance :=
  prepared.facts.context.program.input.mirTables.instance id

private def lookupDefinitionId (lookup : GlobalLookup prepared) (sourceId : DefinitionId) : Result MIR.DefId := do
  match lookup.definitionIndex[(sourceId.crateIndex, sourceId.index)]? with
  | some id => pure id
  | none => throw s!"unresolved compiler definition {sourceId.crateIndex}:{sourceId.index}"

/-- None means a known non-symbolic-function/vtable allocation. Missing image
metadata for an allocation declared symbolic is unresolved evidence, not None. -/
private def sourceNode (image : AllocationImage.Imported) (memory : MemoryState P E K)
    (id : AllocId) : Result (Option AllocationNode) := do
  if memory.hasImportedRuntimeId id then
    return some (← image.sourceNode memory id)
  let info ← (memory.getAllocInfo id).mapError fun error => reprStr error
  if info.kind == .function || info.kind == .vtable then
    throw "symbolic allocation has no imported compiler identity"
  return none

def globalFunctionUsing (prepared : Prepared) (lookup : GlobalLookup prepared)
    (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (id : AllocId) : Result (Option CallInstance) := do
  let some node ← sourceNode image memory id | return none
  let some (.function source) := node.data | return none
  let fnInstance ← functionInstance prepared source.instanceId
  let metadata ← (prepared.facts.context.program.input.mirTables.allocationFunctions.lookup node.id).mapError
    (fun id => s!"global function allocation metadata absent: {id}") >>= (fun result => result)
  unless metadata.instanceId == source.instanceId && metadata.definitionId == source.definitionId do
    throw "global function allocation source identity mismatch"
  let definition ← lookupDefinitionId lookup source.definitionId
  unless fnInstance.defId == definition do throw "global function/full-instance definition mismatch"
  unless metadata.callee == fnInstance do throw "global function/full-instance generic arguments mismatch"
  return some fnInstance

def globalFunction (prepared : Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (id : AllocId) : Result (Option CallInstance) :=
  globalFunctionUsing prepared (GlobalLookup.prepare prepared) image memory id

private def allocationMetadata (facts : CompilerFactAdapters.Prepared) (id : AllocationId) : Result VtableMetadataData := do
  let tables := facts.context.program.input.vtableTables
  let some (some metadata) := tables.allocationMetadata[id]? | throw "allocation vtable metadata absent"
  tables.metadata.lookup metadata |>.mapError (fun id => s!"invalid vtable metadata {id}")

def globalVTable (prepared : Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (id : AllocId) : Result (Option (MIR.TyId × Nat)) := do
  let some node ← sourceNode image memory id | return none
  let some (.vtable source) := node.data | return none
  let _ ← prepared.facts.context.runtime.node source.typeId |>.mapError toString
  let metadata ← allocationMetadata prepared.facts node.id
  unless metadata.typeId == source.typeId do throw "global vtable allocation/type metadata mismatch"
  return some (source.typeId,metadata.predicates)

def globalVTableUsing (prepared : Prepared) (_lookup : GlobalLookup prepared)
    (image : AllocationImage.Imported) (memory : MemoryState P E K) (id : AllocId) :
    Result (Option (MIR.TyId × Nat)) :=
  globalVTable prepared image memory id

private def allocationPrincipal (facts : CompilerFactAdapters.Prepared) (id : Nat) : Result Nat := do
  let source ← CompilerVTableFacts.evidence facts id
  unless source.kind == .trait do throw "vtable principal is not a trait"
  let normalized ← CompilerVTableFacts.normalizePredicate facts ⟨id,source.stableKey,source.autoTrait⟩
  let target ← CompilerVTableFacts.evidence facts normalized
  unless target.kind == .trait do throw "normalized vtable principal is not a trait"
  return normalized

def queryTargetPrincipal (facts : CompilerFactAdapters.Prepared)
    (sourceType allocationId : Nat) : Result Nat := do
  let tables := facts.context.program.input.vtableTables
  let mut found := none
  for source in tables.queries do
    let row ← source
    unless row.allocationId == some allocationId do continue
    unless row.inputTypeId == sourceType do throw "memory-backed supertrait target compiler type mismatch"
    let some id := row.metadata | throw "compiler vtable target row lacks metadata"
    let metadata ← tables.metadata.lookup id |>.mapError (fun id => s!"invalid vtable metadata {id}")
    unless metadata.status == .supported && metadata.layoutStatus == .supported do
      throw "compiler vtable target metadata unavailable"
    let some principal := metadata.principal | throw "compiler vtable target principal absent"
    let normalized ← allocationPrincipal facts principal
    let some size := metadata.sizeBytes | throw "compiler vtable size absent"
    let some align := metadata.alignBytes | throw "compiler vtable alignment absent"
    let evidence := (sourceType,normalized,size,align,metadata.entries)
    if let some previous := found then
      unless previous == evidence do throw "conflicting compiler vtable rows for allocation identity"
    else found := some evidence
  let some (_,principal,_,_,_) := found | throw "compiler vtable query for supertrait allocation absent"
  return principal

/-- Recover the target principal only through the exact serialized compiler
allocation identity. A direct `.vtable` node carries its own type/principal;
rustc may instead serialize the same global allocation as memory, in which
case the query row's `vtable_allocation_id` is the required identity join. -/
def supertraitPrincipal (prepared : Prepared) (sourceType : MIR.TyId)
    (entry : Input.VtableEntryData) : Result Nat := do
  unless entry.status == .supported && entry.kind == .supertraitVtablePointer do
    throw "supertrait vtable entry is unresolved"
  let some sourceId := entry.allocationId | throw "supertrait vtable source allocation missing"
  let nodes := prepared.facts.context.program.input.allocations.filter (·.id == sourceId)
  unless nodes.size == 1 do throw "supertrait vtable allocation identity is missing or ambiguous"
  let some target := nodes[0]? | throw "supertrait vtable allocation evidence missing"
  unless target.status == .supported do throw "supertrait vtable allocation is unresolved"
  match target.kind, target.data with
  | .vtable, some (.vtable vtable) =>
    unless vtable.typeId == sourceType do throw "supertrait vtable concrete type mismatch"
    let metadata ← allocationMetadata prepared.facts target.id
    let some targetPrincipal := metadata.principal | throw "supertrait vtable has no principal"
    return targetPrincipal
  | .memory, some (.memory _) =>
    queryTargetPrincipal prepared.facts sourceType sourceId
  | _, _ => throw "supertrait allocation is neither a compiler vtable nor its memory image"

private def methodInstance (prepared : Prepared)
    (entry : Input.VtableEntryData) : Result CallInstance := do
  let some id := entry.instanceId | throw "vtable method complete instance ID missing"
  functionInstance prepared id

private def entryValue (prepared : Prepared)
    (sourceType : MIR.TyId)
    (entry : Input.VtableEntryData) : Result (Interpreter.VTableEntry CallInstance) := do
  unless entry.status == .supported do throw "compiler vtable entry unresolved"
  match entry.kind with
  | .dropInPlace | .dropInPlaceNull => return .dropInPlace
  | .sizeBytes => return .size
  | .alignBytes => return .align
  | .vacant => return .vacant
  | .method => return .method (← methodInstance prepared entry)
  | .supertraitVtablePointer =>
    let token ← supertraitPrincipal prepared sourceType entry
    return .traitVPtr token
  | .unknown tag => throw s!"unknown compiler vtable entry {tag}"

/-- Actual compiler vtable_entries result keyed by its concrete type and exact
compiler principal. Repeated symbolic allocations must provide identical query
results; allocation-ID coincidence and type-size inference are never keys. -/
def entries (prepared : Prepared)
    (expectedPrincipal : Option Nat) (ty : MIR.TyId) :
    Result (Array (Interpreter.VTableEntry CallInstance)) := do
  let tables := prepared.facts.context.program.input.vtableTables
  let mut found : Option Nat := none
  for node in prepared.facts.context.program.input.allocations do
    if let some (.vtable source) := node.data then
      if source.typeId == ty then
        let metadata ← allocationMetadata prepared.facts node.id
        if metadata.principal == expectedPrincipal then
          if let some previous := found then
            unless previous == metadata.entries do throw "conflicting compiler vtable entry lists"
          else found := some metadata.entries
  for source in tables.queries do
    let row ← source
    unless row.inputTypeId == ty do continue
    let some id := row.metadata | continue
    let metadata ← tables.metadata.lookup id |>.mapError (fun id => s!"invalid vtable metadata {id}")
    unless metadata.principal == expectedPrincipal do continue
    unless metadata.status == .supported && metadata.layoutStatus == .supported do
      throw "compiler vtable runtime metadata unavailable"
    if let some previous := found then
      unless previous == metadata.entries do throw "conflicting compiler vtable entry lists"
    else found := some metadata.entries
  let some id := found | throw "compiler principal/type vtable entries absent"
  let source ← tables.entryLists.lookup id |>.mapError (fun id => s!"invalid vtable entry list {id}")
  source.mapM (entryValue prepared ty)

private def lift (value : Result A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler symbolic allocation query: {error}")

/-- Install imported symbolic allocation queries with canonical machine memory.
Address resolution and vtable-entry/principal queries remain required leaves;
this does not manufacture them from the selected pointer's bytes. -/
def hooks (prepared : Prepared) (image : AllocationImage.Imported)
    (memory : S → MemoryState P E K) (base : VTableHooks P S C CallInstance Abi) :
    VTableHooks P S C CallInstance Abi := Id.run do
  let lookup := GlobalLookup.prepare prepared
  { base with
    entries := fun _ principal ty => lift (entries prepared principal ty)
    globalFunction := fun _ id => do lift (globalFunctionUsing prepared lookup image (memory (← get)) id)
    globalVTable := fun _ id => do lift (globalVTable prepared image (memory (← get)) id) }

end Miri.Input.CompilerVTableRuntime
