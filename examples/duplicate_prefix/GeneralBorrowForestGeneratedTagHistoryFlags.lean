import duplicate_prefix.GeneralBorrowForestGeneratedTagHistoryData
namespace DuplicatePrefix.GeneralBorrowForestGeneratedTagHistoryFlags
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem counter_unheld (state : Snapshot) (initial : Invariant state) : state.global.protectedTags.contains state.global.nextPointerTag=false :=
  (GenericFunctionTagFormation.fresh_above state.tree state.global.protectedTags state.global.nextPointerTag state.global.nextPointerTag
    (GeneralBorrowForestTagHighWater.complete _ _ _ initial.below initial.structural.allocator.nodeTags) (Nat.le_refl _)).2.2

/-- The same actual allocation/register path used by constructor events yields
precisely the requested protection bit and a genuine source-owned singleton
frame. These facts are formed, not after-step flags supplied by the caller. -/
theorem generated (id : AllocId) (state : Snapshot) (initial : Invariant state)
    (fresh : state.global.nextPointerTag.value<18446744073709551615) (held : Bool) :
    let allocated : GlobalState := {state.global with nextPointerTag:=TypedRetagEmpty.successorTag state.global.nextPointerTag fresh}
    let registered := register id state allocated state.global.nextPointerTag held
    state.global.newPointerTag=.ok (allocated,state.global.nextPointerTag) ∧
      registered.global.protectedTags.contains state.global.nextPointerTag=held ∧
      registered.global.nextPointerTag.value.toNat=state.global.nextPointerTag.value.toNat+1 ∧
      (held=true → registered.frames.back?=some (state.global.nextPointerTag,({} : FrameState).addProtector id state.global.nextPointerTag)) := by
  have actual := TypedRetagEmpty.allocate_tag state.global fresh
  have value := GenericFunctionEntryNumerics.successor_value state.global.nextPointerTag fresh
  have unheld := counter_unheld state initial
  refine ⟨actual,?_,?_,?_⟩
  · cases held with
    | false => exact unheld
    | true => simp [register,GlobalState.addProtector,ProtectedTags.contains]
  · cases held <;> exact value
  · cases held <;> simp [register,GlobalState.addProtector]
end DuplicatePrefix.GeneralBorrowForestGeneratedTagHistoryFlags
