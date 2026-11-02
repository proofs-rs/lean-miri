import empty_function.AllocatorActive
import empty_function.ProjectedAllocation
import empty_function.RawResources
namespace EmptyFunction.ProjectedReserveTotal
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

theorem reserve_id (before after : MemoryState Provenance BorrowTree MiriMemoryKind) (id : AllocId)
    (actual : before.reserveAllocId = (after,.ok id)) : id.value = before.nextAllocId := by
  have result := congrArg Prod.snd actual
  unfold MemoryState.reserveAllocId at result
  simp only [Id.run,pure,Pure.pure] at result
  repeat' first | (split at result) | (simp_all [AllocId.ofUInt64])
  all_goals
    have concrete : ∃ h : before.nextAllocId ≠ 0, (⟨before.nextAllocId,h⟩ : AllocId) = id := by assumption
    obtain ⟨_,same⟩ := concrete
    exact (congrArg AllocId.value same).symm

/-- Actual successful reservation provides freshness without numeric headroom;
checked exhaustion remains the exact pure error branch. -/
theorem total (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (needed : InputDraft.NeedsEnclosingAllocation p) :
    (∃ reserved error, p.before.machine.memory.reserveAllocId = (reserved,.error error)) ∨
    (∃ (reserved : MemoryState Provenance BorrowTree MiriMemoryKind) (id : AllocId),
      p.before.machine.memory.reserveAllocId = (reserved,.ok id) ∧
      id.value = p.before.machine.memory.nextAllocId ∧
      reserved.live = p.before.machine.memory.live ∧
      p.before.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id) = false ∧
      p.before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none ∧
      p.before.machine.memory.live.find? (fun row => row.1 == id) = none) := by
  cases reservedEq : p.before.machine.memory.reserveAllocId with
  | mk reserved outcome =>
    cases outcome with
    | error error => exact Or.inl ⟨reserved,error,rfl⟩
    | ok id =>
      have identity := reserve_id _ _ _ reservedEq
      have nonzero : p.before.machine.memory.nextAllocId ≠ 0 := by rw [←identity];exact id.nonzero
      have canonical : id = (⟨p.before.machine.memory.nextAllocId,nonzero⟩ : AllocId) := by
        cases id with
        | mk value nonzeroId => cases identity; rfl
      have representation := input.projectedAllocator needed (AllocatorActive.of_success _ _ _ reservedEq)
      have fields := ProjectedAllocation.reserve_registry p.before.machine.memory
      rw [reservedEq] at fields
      refine Or.inr ⟨reserved,id,rfl,identity,fields.1,?_,?_,?_⟩
      · simpa only [←canonical] using ProjectedAllocation.extras_fresh s p representation nonzero
      · simpa only [←canonical] using RawResources.fresh_base_issued p.before representation nonzero
      · apply Array.find?_eq_none.mpr
        intro row member equal
        have below := representation.live row member
        have same := beq_iff_eq.mp equal
        rw [same,identity] at below
        exact Nat.lt_irrefl _ below
end EmptyFunction.ProjectedReserveTotal
