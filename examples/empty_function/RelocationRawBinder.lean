import empty_function.RelocationInput
namespace EmptyFunction.RelocationRawBinder
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.ChoiceSupply
set_option autoImplicit false
set_option maxHeartbeats 8000000
private theorem length_bound (rows : List (Size × CtfeProvenance)) (limit start : Nat)
    (ordered : rows.Pairwise (fun left right => left.1.bytes.toNat+8 ≤ right.1.bytes.toNat))
    (windows : ∀ row ∈ rows, row.1.bytes.toNat+8 ≤ limit)
    (lower : ∀ row ∈ rows, start ≤ row.1.bytes.toNat) (startBound : start ≤ limit) :
    start+8*rows.length ≤ limit := by
  induction rows generalizing start with
  | nil => simpa using startBound
  | cons row rest ih =>
    have here := windows row (by simp)
    have begin := lower row (by simp)
    have post := ih (row.1.bytes.toNat+8) (List.pairwise_cons.mp ordered).2
      (fun later member => windows later (by simp [member]))
      ((List.pairwise_cons.mp ordered).1) here
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one] at post ⊢
    omega
/-- Raw compiler relocation windows bound the finite loop by physical bytes. -/
theorem count (source : Allocation CtfeProvenance Unit) (physical : InputDraft.CompilerAllocation source) :
    source.provenanceMap.ptrs.size ≤ source.len := by
  have bound := length_bound source.provenanceMap.ptrs.toList source.len 0 physical.ordered
    (fun row member => physical.windows row (by simpa using member)) (by intros;omega) (by omega)
  simp only [Nat.zero_add,Array.length_toList] at bound
  omega
/-- Existing resource bounds cover every raw relocation, without a new budget
field or a bound on a future operational result. -/
theorem count_resources (s : WholeCall.Static) (p : WholeCall.Packet)
    (resources : Specification.ResourceMargins s p) (id : AllocId)
    (source : Allocation CtfeProvenance Unit) (physical : InputDraft.CompilerAllocation source)
    (descriptor : p.before.machine.memory.findGlobal? id = some
      ⟨id,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩) :
    source.provenanceMap.ptrs.size ≤ resources.budget := by
  have bound := resources.globalSizes _ (RelocationResources.global_mem p.before id _ descriptor)
  change source.byteSize.bytes.toNat ≤ resources.maximumSize at bound
  have storage := physical.storage
  have counted := count source physical
  have budget := resources.maximumSizeBudget
  omega

theorem demand_identity (s : WholeCall.Static) (before : WholeCall.State) (id : AllocId)
    (demand : Option AllocId) (relation : SourceChoicePlan.Demand s before id demand)
    (value : Allocation CtfeProvenance Unit)
    (descriptor : before.machine.memory.findGlobal? id = some
      ⟨id,.memory,value.byteSize,value.align,value.mutability,some (.memory value)⟩) : demand = some id := by
  cases relation with
  | direct _ _ => rfl
  | foreign global definition backing query payload _ =>
    have equal := Option.some.inj (query.symm.trans descriptor)
    cases equal
    cases payload
/-- The actual raw demand binding keeps every ordinary memory target and
its duplicate occurrence in source order. -/
theorem demands (s : WholeCall.Static) (before : WholeCall.State)
    (rows : List (Size × CtfeProvenance)) (ds : List (Option AllocId))
    (relation : SourceChoicePlan.Rows (fun row demand => SourceChoicePlan.Demand s before row.2.allocId demand) rows ds)
    (targets : ∀ row ∈ rows, ∃ value : Allocation CtfeProvenance Unit,
      before.machine.memory.findGlobal? row.2.allocId = some
        ⟨row.2.allocId,.memory,value.byteSize,value.align,value.mutability,some (.memory value)⟩) :
    ds = rows.map (fun row => some row.2.allocId) := by
  induction relation with
  | nil => rfl
  | @cons row demand rows ds head tail ih =>
    obtain ⟨value,descriptor⟩ := targets row (by simp)
    have here := demand_identity s before row.2.allocId demand head value descriptor
    rw [here,ih (fun later member => targets later (by simp [member]))]
    rfl
end EmptyFunction.RelocationRawBinder
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.RelocationRawBinder.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved relocation raw binder axiom {dependency} in {name}"
