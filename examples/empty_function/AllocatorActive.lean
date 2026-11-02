import Miri.Memory.MemoryState
namespace EmptyFunction.AllocatorActive
open Miri Miri.Memory
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

def Active {Prov Extra MachineKind : Type} (memory : MemoryState Prov Extra MachineKind) : Prop :=
  memory.idSupplyExhausted = false ∧ memory.nextAllocId ≠ 0 ∧
    (memory.sourceAllocIdWorldActive = true →
      memory.sourceAllocIdExhausted = false ∧ memory.sourceAllocIdNext ≠ 0)

theorem of_success {Prov Extra MachineKind : Type}
    (before after : MemoryState Prov Extra MachineKind) (id : AllocId)
    (actual : before.reserveAllocId = (after,.ok id)) : Active before := by
  have result := congrArg Prod.snd actual
  unfold MemoryState.reserveAllocId at result
  simp only [Id.run,pure,Pure.pure] at result
  unfold Active
  repeat' first | (split at result) | (simp_all [AllocId.ofUInt64,Bool.or_eq_false_iff,Bool.and_eq_true])

  all_goals
    have canonical : ∃ h : before.nextAllocId ≠ 0, (⟨before.nextAllocId,h⟩ : AllocId) = id := by assumption
    exact canonical.choose

open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``of_success) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved allocator-active axiom {dependency}"
#print axioms of_success
end EmptyFunction.AllocatorActive
