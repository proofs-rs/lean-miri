import empty_function.Specification
import empty_function.RelocationInput
import empty_function.RawRootAdmission
namespace EmptyFunction.StaticSourceInput
open Miri Miri.ABI Miri.Memory Miri.Interpreter
open EmptyFunction.WholeCall
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

/-- Any selected concrete/wildcard runtime pointer carries the current address
tables, even when no address-generation state exists. -/
theorem tables (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (id : AllocId) (selected : ChoiceAdmission.SelectedId p id) : InputDraft.AddressTables p.before := by
  cases selected with
  | concrete pointer tag effective provenance =>
    have pointerInput := input.effective pointer effective
    cases pointerInput with
    | integer encoding => rw [provenance] at encoding;cases encoding
    | concrete _ _ _ tables _ _ _ _ _ => exact tables
    | wildcard encoding _ _ _ => rw [provenance] at encoding;cases encoding
  | wildcard pointer row effective provenance _ _ _ _ =>
    have pointerInput := input.effective pointer effective
    cases pointerInput with
    | integer encoding => rw [provenance] at encoding;cases encoding
    | concrete _ _ _ _ encoding _ _ _ _ => rw [provenance] at encoding;cases encoding
    | wildcard _ _ tables _ => exact tables

/-- Selected internal-static payloads already carry the exact source format
and target representation facts in the original raw current input. -/
theorem facts (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (id : AllocId) (definition : Nat) (source : Allocation CtfeProvenance Unit)
    (selected : ChoiceAdmission.SelectedId p id)
    (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
    (noVaList : p.before.machine.memory.hasVaListId id = false)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
    (initializer : s.prepared.image.initializers.find? (·.1 == definition) = some (definition,source)) :
    InputDraft.RelocationInput s p.before source ∧
      p.before.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false := by
  have backing := RelocationInput.selected_backing s p input id selected
  cases backing with
  | live entry row => rw [absent] at row;cases row
  | global entry query _ content _ vacant =>
    have same := Option.some.inj (query.symm.trans descriptor)
    cases same
    refine ⟨?_,vacant absent (Or.inr rfl)⟩
    cases content with
    | memory _ kind _ _ _ _ _ => cases kind
    | internalStatic actualDef actualSource kind payload actualInitializer _ _ _ sourceInput =>
      have sameDef : actualDef = definition := by simpa using payload.symm
      subst actualDef
      have sameSource : actualSource = source :=
        (Prod.mk.inj (Option.some.inj (actualInitializer.symm.trans initializer))).2
      cases sameSource
      exact sourceInput
    | externalStatic _ _ payload => simp at payload
    | threadLocalStatic _ _ _ payload => simp at payload
    | function kind => cases kind
    | vtable kind => cases kind
    | typeId kind => cases kind
  | extraFunction row =>
    unfold MemoryState.hasExtraFunctionId at row
    have impossible : p.before.machine.memory.hasFunctionPointer id = true := by
      simp only [MemoryState.hasFunctionPointer,row,Bool.true_or]
    rw [noFunction] at impossible
    cases impossible
  | vaList row => rw [noVaList] at row;cases row
  | dead _ _ _ _ _ noGlobal => rw [descriptor] at noGlobal;cases noGlobal

/-- The existing supplied-policy environment already selects internal statics;
no memory descriptor or replacement caller packet is manufactured. -/
theorem environment (s : Static) (p : Packet) (resources : Specification.ResourceMargins s p)
    (id : AllocId) (definition : Nat) (source : Allocation CtfeProvenance Unit)
    (selected : ChoiceAdmission.SelectedId p id)
    (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
    (noVaList : p.before.machine.memory.hasVaListId id = false)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
    (initializer : s.prepared.image.initializers.find? (·.1 == definition) = some (definition,source)) :
    ∃ binding : SourceChoicePlan.Binding s p.before source, SourceChoicePlan.Environment binding :=
  resources.choices.latent id source (.internalStatic definition selected absent noFunction noVaList descriptor initializer)

/-- The same raw descriptor selects general policy supply, retaining every
seed and the actual fallback plan. -/
theorem policy_environment (s : Static) (p : Packet) (resources : Specification.PolicyResourceMargins s p)
    (id : AllocId) (definition : Nat) (source : Allocation CtfeProvenance Unit)
    (selected : ChoiceAdmission.SelectedId p id)
    (absent : p.before.machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : p.before.machine.memory.hasFunctionPointer id = false)
    (noVaList : p.before.machine.memory.hasVaListId id = false)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
    (initializer : s.prepared.image.initializers.find? (·.1 == definition) = some (definition,source)) :
    ∃ binding : SourceChoicePlan.Binding s p.before source, SourceChoicePlan.PolicyEnvironment binding :=
  resources.choices.latent id source (.internalStatic definition selected absent noFunction noVaList descriptor initializer)

private theorem member_le_sum (values : List Nat) (value : Nat) (member : value ∈ values) : value ≤ values.sum := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with same | later
    · subst value;simp only [List.sum_cons];omega
    · have bound := ih later;simp only [List.sum_cons];omega

/-- The initializer occurs explicitly in the existing work count, so its
arbitrary finite relocation list retains the same fixed reserve. -/
theorem spare (s : Static) (p : Packet) (condition : Prop)
    (resources : Specification.ResourceMargins s p condition)
    (definition : Nat) (source : Allocation CtfeProvenance Unit)
    (initializer : s.prepared.image.initializers.find? (·.1 == definition) = some (definition,source)) :
    source.provenanceMap.ptrs.size+64 ≤ resources.budget := by
  have member := Array.mem_of_find?_eq_some initializer
  have counted : source.len+source.provenanceMap.ptrs.size ∈
      (s.prepared.image.initializers.toList.map fun row => row.2.len+row.2.provenanceMap.ptrs.size) := by
    apply List.mem_map.mpr
    exact ⟨(definition,source),by simpa using member,rfl⟩
  have bound := member_le_sum _ _ counted
  have reserve := resources.reserve
  unfold Specification.work at reserve
  omega
/-- Normal target metadata bounds follow from the original tables and numeric
resources. Only the source's registered alignment supplies the nonzero bound;
no memory-kind descriptor is needed for the source. -/
theorem info_bounds (s : Static) (p : Packet) (condition : Prop)
    (resources : Specification.ResourceMargins s p condition)
    (sourceId : AllocId) (definition : Nat) (source : Allocation CtfeProvenance Unit)
    (sourceDescriptor : p.before.machine.memory.findGlobal? sourceId = some
      ⟨sourceId,.static,source.byteSize,source.align,source.mutability,some (.static definition true false false)⟩)
    (id : AllocId) (info : AllocationInfo)
    (admission : RawRootAdmission.Normal p.before.machine.memory id)
    (metadata : p.before.machine.memory.getAllocInfo id = .ok info) :
    info.kind ≠ .dead ∧ info.size.bytes.toNat ≤ resources.maximumSize ∧
      2^info.align.pow2 ≤ resources.maximumAlignment := by
  have registered := RelocationResources.global_mem p.before sourceId _ sourceDescriptor
  have sourceAlign := resources.globalAlignments _ registered
  have alignPositive : 1 ≤ resources.maximumAlignment := by
    have positive : 0 < (2:Nat)^source.align.pow2 := Nat.pow_pos (by decide)
    change 2^source.align.pow2 ≤ resources.maximumAlignment at sourceAlign
    omega
  unfold MemoryState.getAllocInfo at metadata
  cases located : p.before.machine.memory.live.find? (fun row => row.1 == id) with
  | some row =>
    simp only [located,pure,Except.pure] at metadata
    cases metadata
    refine ⟨by simp,?_,?_⟩
    · exact resources.liveByteSizes row (Array.mem_of_find?_eq_some located)
    · exact resources.liveAlignments row (Array.mem_of_find?_eq_some located)
  | none =>
    simp only [located] at metadata
    by_cases function : p.before.machine.memory.hasFunctionPointer id = true
    · simp only [function,↓reduceIte,pure,Except.pure] at metadata
      cases metadata
      exact ⟨by simp,Nat.zero_le _,alignPositive⟩
    · simp only [function] at metadata
      by_cases va : p.before.machine.memory.hasVaListId id = true
      · unfold MemoryState.hasVaListId at va
        simp only [va,↓reduceIte,pure,Except.pure] at metadata
        cases metadata
        exact ⟨by simp,Nat.zero_le _,alignPositive⟩
      · unfold MemoryState.hasVaListId at va
        simp only [va,Bool.false_eq_true,↓reduceIte] at metadata
        cases descriptor : p.before.machine.memory.findGlobal? id with
        | none =>
          rcases admission.supplier with ⟨global,query⟩ | extra | listed
          · rw [descriptor] at query; cases query
          · unfold MemoryState.hasExtraFunctionId at extra
            have impossible : p.before.machine.memory.hasFunctionPointer id = true := by
              simp only [MemoryState.hasFunctionPointer,extra,Bool.true_or]
            exact False.elim (function impossible)
          · unfold MemoryState.hasVaListId at listed
            exact False.elim (va listed)
        | some global =>
          have member := RelocationResources.global_mem p.before id global descriptor
          simp only [descriptor] at metadata
          cases kind : global.kind <;> simp only [kind,pure,Except.pure] at metadata <;> cases metadata
          all_goals first
            | exact ⟨by simp,Nat.zero_le _,alignPositive⟩
            | exact ⟨by simp,Nat.zero_le _,resources.globalAlignments global member⟩
            | exact ⟨by simp,resources.globalSizes global member,resources.globalAlignments global member⟩

end EmptyFunction.StaticSourceInput

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.StaticSourceInput.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved static source input axiom {name}: {dependency}"
