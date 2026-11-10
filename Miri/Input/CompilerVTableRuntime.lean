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
    (id : Nat) : Result Nat := do
  let sources := facts.context.program.input.compilerPredicates.filter (·.id == id)
  let some source := sources[0]? | throw "memory-backed vtable principal normalization evidence missing"
  unless sources.all (· == source) && source.original == id do
    throw "memory-backed vtable principal conflicts with normalization evidence"
  let normalized ← CompilerVTableFacts.normalizePredicate facts ⟨id,source.stableKey,source.autoTrait⟩
  let targets := facts.context.program.input.compilerPredicates.filter (·.id == normalized)
  let some target := targets[0]? | throw "normalized memory-backed vtable principal evidence missing"
  let some targetDefinition := facts.context.program.input.predicates[target.original]?
    | throw "normalized compiler principal predicate ID out of bounds"
  unless targets.all (· == target) && targetDefinition.kind == .trait do
    throw "normalized memory-backed vtable principal evidence conflicts"
  return normalized

def queryTargetPrincipal (facts : CompilerFactAdapters.Prepared)
    (queries : Array Catalog.VtableQuery) (sourceType allocationId : Nat) : Result Nat := do
  let mut found : Option (Nat × Nat × Option Nat × Option Nat × Array Input.VtableEntry) := none
  for row in queries do
    unless row.vtableAllocation == some allocationId do continue
    unless row.inputType == sourceType do throw "memory-backed supertrait target compiler type mismatch"
    let metadata := row.metadata
    unless metadata.typeId == sourceType do throw "memory-backed supertrait target metadata type mismatch"
    unless metadata.predicates == row.inputPredicates do
      throw "memory-backed supertrait target predicates disagree with query key"
    let some predicateId := metadata.principalPredicate
      | throw "memory-backed supertrait target has no supported principal trait"
    let some definition := facts.context.program.input.predicates[predicateId]?
      | throw "compiler principal predicate ID out of bounds"
    unless definition.kind == .trait do throw "memory-backed supertrait target has no supported principal trait"
    let targetPrincipal ← allocationPrincipal facts predicateId
    let some size := metadata.sizeBytes | throw "memory-backed vtable size is absent"
    let some align := metadata.alignBytes | throw "memory-backed vtable alignment is absent"
    let evidence := (targetPrincipal, metadata.typeId, some size, some align, metadata.entries)
    if let some previous := found then
      unless previous == evidence do throw "conflicting compiler vtable rows for exact allocation identity"
    else found := some evidence
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
    queryTargetPrincipal prepared.facts prepared.facts.context.program.input.queries.vtables sourceType sourceId
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
            unless previous == source.entries do
              throw "conflicting compiler vtable_entries queries"
          else found := some source.entries
  for row in prepared.facts.context.program.input.queries.vtables do
    unless row.inputType == ty do continue
    let metadata := row.metadata
    unless metadata.principalPredicate == expectedPrincipal do continue
    unless metadata.predicates == row.inputPredicates do
      throw "compiler vtable metadata predicate identity disagrees with its query key"
    unless metadata.typeId == ty do throw "compiler vtable metadata type disagrees with its query key"
    if let some previous := found then
      unless previous == metadata.entries do throw "conflicting source compiler vtable_entries query metadata"
    else found := some metadata.entries
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
