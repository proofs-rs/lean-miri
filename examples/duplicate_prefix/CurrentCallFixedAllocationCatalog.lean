import duplicate_prefix.Prepared
import duplicate_prefix.GlobalAllocationAttributes

/-! Facts about the ACTUAL imported allocation image only. They do not assert
that an arbitrary current machine's global table equals the initial catalog,
or exclude historical type/allocation-cache entries. -/
namespace DuplicatePrefix.CurrentCallFixedAllocationCatalog
open Lean Miri Miri.ABI Miri.Input Miri.Memory
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

open Lean Elab Command in
run_cmd do
  let hash ← IO.Process.output {cmd:="sha256sum",args:=#["examples/duplicate_prefix/input.json"]}
  unless hash.exitCode == 0 && hash.stdout.startsWith "444638d5f40f4e59df584939ed6479272ecea1ca9244de2f9e5152ab7f459f06 " do
    throwError "fixed allocation catalog input hash mismatch"

def memoryReadonly (descriptor : GlobalAllocation) : Bool :=
  descriptor.kind == .memory && descriptor.mutability == .Not &&
    match descriptor.payload with
    | some (.memory source) => source.mutability == .Not
    | _ => false

/-- All real initial global descriptors are immutable memory images; this is
not a no-global theorem. -/
theorem catalog_grammar : PreparedReflection.actual.initialMemory.globals.all memoryReadonly=true := by decide +kernel

theorem catalog_size : PreparedReflection.actual.initialMemory.globals.size=718 := by rfl

theorem static_initializers_empty : PreparedReflection.actual.image.initializers=#[] := by rfl

private theorem keyed_find_mem {K V : Type} [BEq K] [Hashable K] {keyOf : V→K}
    (table : KeyedArray K V keyOf) (key : K) (value : V) (found : table.find? key=some value) :
    value∈table.toArray := by
  rcases table with ⟨keys,rows,index,exact,aligned,agrees⟩
  unfold KeyedArray.find? at found
  dsimp only at found
  change ((index.2.get? key).bind (fun positions=>positions[0]?.bind (fun position=>rows[position]?)))=some value at found
  cases lookup : index.2.get? key with
  | none => simp only [lookup,Option.bind_none] at found;cases found
  | some positions =>
    cases first : positions[0]? with
    | none => simp only [lookup,Option.bind_some,first,Option.bind_none] at found;cases found
    | some position =>
      have atRow : rows[position]?=some value := by simpa only [lookup,Option.bind_some,first] using found
      exact Array.mem_of_getElem? atRow

private theorem global_find_mem {P E K : Type} (memory : MemoryState P E K)
    (id : AllocId) (descriptor : GlobalAllocation) (found : memory.findGlobal? id=some descriptor) :
    descriptor∈memory.globals := by
  unfold MemoryState.findGlobal? at found
  unfold MemoryState.globals
  exact keyed_find_mem _ _ _ found

/-- Consume the REAL selected initial-memory query. No supplied descriptor or
fabricated compiler-query function replaces the interpreter lookup. -/
theorem initial_query (id : AllocId) (descriptor : GlobalAllocation)
    (selected : PreparedReflection.actual.initialMemory.findGlobal? id=some descriptor) :
    descriptor.kind=.memory ∧ descriptor.mutability=.Not ∧
      ∃ source,descriptor.payload=some (.memory source) ∧ source.mutability=.Not := by
  have member := global_find_mem _ id descriptor selected
  obtain ⟨position,bound,equal⟩ := Array.mem_iff_getElem.mp member
  have grammar := (Array.all_eq_true.mp catalog_grammar) position bound
  rw [equal] at grammar
  unfold memoryReadonly at grammar
  have parts := Bool.and_eq_true_iff.mp grammar
  have left := Bool.and_eq_true_iff.mp parts.1
  refine ⟨beq_iff_eq.mp left.1,beq_iff_eq.mp left.2,?_⟩
  cases payload : descriptor.payload with
  | none => simp [payload] at grammar
  | some value =>
    cases value with
    | memory source => exact ⟨source,rfl,beq_iff_eq.mp (by simpa only [payload] using parts.2)⟩
    | function | vtable | typeId | static _ _ _ _ => simp [payload] at grammar

def sourceReadonly (node : AllocationNode) : Bool :=
  decide (node.kind=.memory) && match node.memory with
    | some memory => decide (memory.mutability=.immutable)
    | none => false

theorem source_grammar : PreparedReflection.actual.image.source.all sourceReadonly=true := by decide +kernel

open Lean Elab Tactic in
elab "unfold_image_lookup" : tactic => do
  for suffix in ["AllocationImage.Imported.findSourceNode?","AllocationImage.Imported.sourceIndex"] do
    let names := (← getEnv).constants.toList.filterMap fun (name,_) =>
      if name.toString.endsWith suffix then some name else none
    let [name] := names | throwError "actual private source lookup is not unique"
    withMainContext do
      let some hypothesis := (← getLCtx).findFromUserName? (Name.mkSimple "selected")
        | throwError "actual selected source query is absent"
      Lean.Elab.Tactic.unfoldLocalDecl name hypothesis.fvarId

/-- This REAL imported-image query first resolves the CURRENT runtime ID
through importedGraphIdForRuntime?, then selects the fixed source node. It
makes no assertion that current global descriptors correspond to that node. -/
theorem source_query {P E K : Type} (memory : MemoryState P E K) (id : AllocId) (node : AllocationNode)
    (selected : PreparedReflection.actual.image.sourceNode memory id=.ok node) :
    node.kind=.memory ∧ ∃ source,node.memory=some source ∧ source.mutability=.immutable := by
  unfold AllocationImage.Imported.sourceNode at selected
  cases graphId : memory.importedGraphIdForRuntime? id with
  | none => simp [graphId] at selected
  | some exported =>
    simp only [graphId,pure] at selected
    unfold_image_lookup
    have actualImage : PreparedReflection.actual.image=AllocationImage.Imported.ofSource
        PreparedReflection.actual.image.source PreparedReflection.actual.image.initializers := rfl
    rw [actualImage] at selected
    simp only [AllocationImage.Imported.ofSource] at selected
    change ((match PreparedReflection.actual.image.source.find? (fun row=>row.id==exported) with
      | some actual => (pure actual : Except String AllocationNode)
      | _ => (throw "imported global source node is unavailable" : Except String AllocationNode)) : Except String AllocationNode)=Except.ok node at selected
    cases lookup : PreparedReflection.actual.image.source.find? (fun row=>row.id==exported) with
    | none => rw [lookup] at selected;cases selected
    | some actual =>
      rw [lookup] at selected
      have same : actual=node := Except.ok.inj selected
      have member := Array.mem_of_find?_eq_some lookup
      obtain ⟨position,bound,equal⟩ := Array.mem_iff_getElem.mp member
      have grammar := (Array.all_eq_true.mp source_grammar) position bound
      rw [equal,same] at grammar
      unfold sourceReadonly at grammar
      have parts := Bool.and_eq_true_iff.mp grammar
      refine ⟨of_decide_eq_true parts.1,?_⟩
      cases source : node.memory with
      | none => simp [source] at grammar
      | some allocation => exact ⟨allocation,rfl,of_decide_eq_true (by simpa only [source] using parts.2)⟩

/-- The actual fixed static-initializer query has no successful branch, even
if an arbitrary current memory table contains a static descriptor. -/
theorem static_query {S : Type} (state : S) (definition : Nat) :
    PreparedReflection.actual.image.evaluateStaticInitializer state definition =
      ⟨state,.error s!"missing compiler static initializer query for definition {definition}"⟩ := by
  unfold AllocationImage.Imported.evaluateStaticInitializer
  rw [static_initializers_empty]
  rfl

/-- Actual materialization attributes retain the imported read-only flag.
No UnsafeCell rule or permission-tree state turns allocation mutability on. -/
theorem converted_readonly (id : AllocId) (descriptor : GlobalAllocation)
    (selected : PreparedReflection.actual.initialMemory.findGlobal? id=some descriptor)
    (source : Allocation CtfeProvenance Unit) (payload : descriptor.payload=some (.memory source))
    (converted : Allocation Provenance Unit) (attributes : GlobalAllocationAttributes.Attributes source converted) :
    converted.mutability=.Not := by
  obtain ⟨_,_,actual,actualPayload,readonly⟩ := initial_query id descriptor selected
  have same : actual=source := GlobalAllocationPayload.memory.inj (Option.some.inj (actualPayload.symm.trans payload))
  exact attributes.mutability.trans (same ▸ readonly)

/-- Read-only imported conversion is incompatible with an explicitly writable
positive storage target. This does not assert that conversion was skipped. -/
theorem converted_not_writable (id : AllocId) (descriptor : GlobalAllocation)
    (selected : PreparedReflection.actual.initialMemory.findGlobal? id=some descriptor)
    (source : Allocation CtfeProvenance Unit) (payload : descriptor.payload=some (.memory source))
    (converted : Allocation Provenance Unit) (attributes : GlobalAllocationAttributes.Attributes source converted)
    (writable : converted.mutability=.Mut) : False := by
  have readonly := converted_readonly id descriptor selected source payload converted attributes
  rw [writable] at readonly
  cases readonly

end DuplicatePrefix.CurrentCallFixedAllocationCatalog
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallFixedAllocationCatalog" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved fixed catalog dependency {dependency}"
