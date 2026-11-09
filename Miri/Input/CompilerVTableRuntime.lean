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

/-- Canonical instances remain in the input table. Preparation creates no
second identity table or semantic instance graph. -/
def prepare (facts : CompilerFactAdapters.Prepared) : Prepared := ⟨facts,#[]⟩

def functionInstance (prepared : Prepared) (id : InstanceId) : Result CallInstance := do
  let _ ← CompilerInstance.source prepared.facts.context.loweringContext id
  pure id

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

def globalFunction (prepared : Prepared)
    (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (id : AllocId) : Result (Option CallInstance) := do
  let some node ← sourceNode image memory id | return none
  let some (.function source) := node.data | return none
  let fnInstance ← functionInstance prepared source.instanceId
  return some fnInstance

def globalVTable (prepared : Prepared) (image : AllocationImage.Imported)
    (memory : MemoryState P E K) (id : AllocId) : Result (Option (MIR.TyId × PredicateList)) := do
  let some node ← sourceNode image memory id | return none
  let some (.vtable source) := node.data | return none
  let _ ← prepared.facts.context.runtime.node source.typeId |>.mapError toString
  pure (some (source.typeId,source.predicates))

private def principal (source : VtableAllocation) : Result (Option Nat) :=
  pure source.principalPredicate

/-- vtable_allocation is queried with an instantiated principal, unlike a
symbolic vtable's full higher-ranked predicate list. Use the compiler's exact
late-bound-erasure/normalization evidence; never compare names or discard the
predicate identity on the original symbolic query. -/
private def allocationPrincipal (facts : CompilerFactAdapters.Prepared)
    (value : Json) : Result (Nat × Json) := do
  let id ← value.getNat?
  let sources := facts.context.program.input.compilerPredicates.filter (·.id == id)
  let some source := sources[0]? | throw "memory-backed vtable principal normalization evidence missing"
  unless sources.all (·.payload == source.payload) && source.original == id do
    throw "memory-backed vtable principal conflicts with normalization evidence"
  let normalized ← CompilerVTableFacts.normalizePredicate facts ⟨id,source.stableKey,source.autoTrait⟩
  let targets := facts.context.program.input.compilerPredicates.filter (·.id == normalized)
  let some target := targets[0]? | throw "normalized memory-backed vtable principal evidence missing"
  let some targetDefinition := facts.context.program.input.predicates[target.original]?
    | throw "normalized compiler principal predicate ID out of bounds"
  unless targets.all (·.payload == target.payload) &&
      targetDefinition.kind == .trait do
    throw "normalized memory-backed vtable principal evidence conflicts"
  return (normalized, toJson target.original)

/-- Resolve a memory-backed vtable through the exact compiler allocation ID
recorded for a principal/type query. Query metadata alone is not enough: the
source TraitVPtr allocation must equal this ID. Each row must agree with its
complete predicate key, while rows sharing the allocation must agree on the
allocation's type, compiler-normalized principal, layout, and entries. A named
HRTB and its instantiated principal can legitimately share this memory image;
their symbolic type/predicate/salt keys remain distinct. -/
def queryTargetPrincipal (facts : CompilerFactAdapters.Prepared)
    (raw : Json) (sourceType allocationId : Nat) : Result Nat := do
  let queryRows ← (← raw.getObjVal? "compiler_vtable_queries").getArr?
  let mut found : Option (Nat × Json) := none
  for (row, rowIndex) in queryRows.toList.zipIdx do
    unless (row.getObjValAs? Nat "vtable_allocation_id").toOption == some allocationId do
      continue
    let rowType ← (← row.getObjVal? "input_type").getNat?
    unless rowType == sourceType do
      throw "memory-backed supertrait target compiler type mismatch"
    let some metadata := (row.getObjVal? "vtable_metadata").toOption
      | throw s!"compiler vtable target row {rowIndex} lacks metadata"
    let metadataType ← metadata.getObjVal? "type"
    unless ((metadataType.getNat?).toOption == some sourceType) do
      throw "memory-backed supertrait target metadata type mismatch"
    let metadataPredicates ← (metadata.getObjVal? "predicates").bind Json.getArr?
    let rowPredicates ← (row.getObjVal? "input_predicates").bind Json.getArr?
    unless metadataPredicates == rowPredicates do
      throw "memory-backed supertrait target predicates disagree with query key"
    let principalPredicate ← metadata.getObjVal? "principal_predicate"
    unless principalPredicate != Json.null do
      throw "memory-backed supertrait target has no supported principal trait"
    let predicateId ← principalPredicate.getNat?
    let some definition := facts.context.program.input.predicates[predicateId]?
      | throw "compiler principal predicate ID out of bounds"
    unless definition.kind == .trait do
      throw "memory-backed supertrait target has no supported principal trait"
    let (targetPrincipal, allocationPredicate) ← allocationPrincipal facts principalPredicate
    let entries ← metadata.getObjVal? "entries"
    let _ ← entries.getArr?
    let size ← (metadata.getObjVal? "size_bytes").bind Json.getNat?
    let align ← (metadata.getObjVal? "align_bytes").bind Json.getNat?
    let evidence := Json.mkObj [
      ("type", metadataType),
      ("principal_predicate", allocationPredicate),
      ("size_bytes", toJson size),
      ("align_bytes", toJson align),
      ("entries", entries)]
    if let some (previousPrincipal, previousEvidence) := found then
      unless previousPrincipal == targetPrincipal && previousEvidence == evidence do
        throw "conflicting compiler vtable rows for exact allocation identity"
    else
      found := some (targetPrincipal, evidence)
  let some (targetPrincipal, _) := found
    | throw "exact compiler vtable query for supertrait allocation is missing"
  return targetPrincipal

/-- Recover the target principal only through the exact serialized compiler
allocation identity. A direct `.vtable` node carries its own type/principal;
rustc may instead serialize the same global allocation as memory, in which
case the query row's `vtable_allocation_id` is the required identity join. -/
def supertraitPrincipal (prepared : Prepared) (sourceType : MIR.TyId)
    (entry : Input.VtableEntry) : Result Nat := do
  unless entry.kind == .supertraitVtablePointer do
    throw "supertrait vtable entry is unresolved"
  let some sourceId := entry.allocationId | throw "supertrait vtable source allocation missing"
  let nodes := prepared.facts.context.program.input.allocations.filter (·.id == sourceId)
  unless nodes.size == 1 do throw "supertrait vtable allocation identity is missing or ambiguous"
  let some target := nodes[0]? | throw "supertrait vtable allocation evidence missing"
  match target.kind, target.data with
  | .vtable, some (.vtable vtable) =>
    unless vtable.typeId == sourceType do throw "supertrait vtable concrete type mismatch"
    let some targetPrincipal ← principal vtable
      | throw "supertrait vtable has no principal"
    return targetPrincipal
  | .memory, some (.memory _) =>
    queryTargetPrincipal prepared.facts prepared.facts.context.program.input.raw sourceType sourceId
  | _, _ => throw "supertrait allocation is neither a compiler vtable nor its memory image"

private def methodInstance (prepared : Prepared)
    (entry : Input.VtableEntry) : Result CallInstance := do
  let some id := entry.instanceId | throw "vtable method complete instance ID missing"
  let fnInstance ← functionInstance prepared id
  return fnInstance

private def entryValue (prepared : Prepared)
    (sourceType : MIR.TyId)
    (entry : Input.VtableEntry) : Result (Interpreter.VTableEntry CallInstance) := do
  match entry.kind with
  | .dropInPlace | .dropInPlaceNull => return .dropInPlace
  | .sizeBytes => return .size
  | .alignBytes => return .align
  | .vacant => return .vacant
  | .method => return .method (← methodInstance prepared entry)
  | .supertraitVtablePointer =>
    let token ← supertraitPrincipal prepared sourceType entry
    return .traitVPtr token

/-- Actual compiler vtable_entries result keyed by its concrete type and exact
compiler principal. Repeated symbolic allocations must provide identical query
results; allocation-ID coincidence and type-size inference are never keys. -/
def entries (prepared : Prepared)
    (expectedPrincipal : Option Nat) (ty : MIR.TyId) :
    Result (Array (Interpreter.VTableEntry CallInstance)) := do
  let mut found : Option (Array Input.VtableEntry) := none
  for node in prepared.facts.context.program.input.allocations do
    if let some (.vtable source) := node.data then
      if source.typeId == ty then
        if (← principal source) == expectedPrincipal then
          if let some previous := found then
            unless previous.map (·.payload) == source.entries.map (·.payload) do
              throw "conflicting compiler vtable_entries queries"
          else found := some source.entries
  let raw := prepared.facts.context.program.input.raw
  let queryRows ← (← raw.getObjVal? "compiler_vtable_queries").getArr?
  for (row, rowIndex) in queryRows.toList.zipIdx do
    let some rowType := (row.getObjVal? "input_type").toOption | continue
    unless ((rowType.getNat?).toOption == some ty) do continue
    let some metadata := (row.getObjVal? "vtable_metadata").toOption | continue
    let predicate := (metadata.getObjVal? "principal_predicate").toOption.getD .null
    let rowPrincipal ← if predicate == .null then pure none else
      predicate.getNat? |>.map some
    unless rowPrincipal == expectedPrincipal do continue
    let metadataPredicates ← (metadata.getObjVal? "predicates").bind Json.getArr?
    let rowPredicates ← (row.getObjVal? "input_predicates").bind Json.getArr?
    unless metadataPredicates == rowPredicates do
      throw "compiler vtable metadata predicate identity disagrees with its query key"
    let metadataType ← metadata.getObjVal? "type"
    unless ((metadataType.getNat?).toOption == some ty) do
      throw "compiler vtable metadata type disagrees with its query key"
    let entryJson ← (metadata.getObjVal? "entries").bind Json.getArr?
    let mut sourceEntries := #[]
    for (entry, index) in entryJson.toList.zipIdx do
      sourceEntries := sourceEntries.push (← Input.decodeVtableEntry entry
        s!"$.compiler_vtable_queries[{rowIndex}].vtable_metadata.entries[{index}]")
    if let some previous := found then
      unless previous.map (·.payload) == sourceEntries.map (·.payload) do
        throw "conflicting source compiler vtable_entries query metadata"
    else found := some sourceEntries
  let some source := found | throw "exact compiler principal/type vtable_entries query missing"
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
    VTableHooks P S C CallInstance Abi :=
  { base with
    entries := fun _ principal ty => lift (entries prepared principal ty)
    globalFunction := fun _ id => do lift (globalFunction prepared image (memory (← get)) id)
    globalVTable := fun _ id => do lift (globalVTable prepared image (memory (← get)) id) }

end Miri.Input.CompilerVTableRuntime
