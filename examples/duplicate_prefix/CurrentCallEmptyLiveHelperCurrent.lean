import duplicate_prefix.CurrentCallZeroSharedBoolWindow
import duplicate_prefix.CurrentCallEmptyLiveHelperFacets
import duplicate_prefix.S03EmptyPositiveTreeFacts
namespace DuplicatePrefix.CurrentCallEmptyLiveHelperCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
/-- Install the retained Bool family after the SAME two real zero helpers.
All tag/order/allocator side conditions are derived from the original current
runtime and the actual helper counter equation. Only the actual final heap
presence is used; there is no invented intermediate heap. -/
theorem window {before tracker data owner id offset}
    (B : UniformWindow before tracker data owner id offset 1 .ret)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (parentTag : BorTag) (first : EmptyForestSharedPool.Input B.allocation.extra parentTag tracker.global.nextPointerTag)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (room : B.allocation.extra.nodes.size+2≤4294967295)
    (post : Before) (next : MachineHooks.BorrowState)
    (globalShape : next.global={tracker.global with nextPointerTag:=next.global.nextPointerTag})
    (nextNat : next.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+2)
    (present : Present (ActualWorld post) id
      (B.allocation.setExtra (S03EmptyNextLenInput.form B.allocation.extra tracker.global runtime parentTag first fresh room).after))
    (original : PointerInstance) (oldBinding : PointerBinds B.allocation original)
    (oldIssued : SpatialDelegation before tracker id B.allocation B.precise.completion original.grant)
    (start : UInt64) (startEq : start.toNat=offset) :
    let second:=S03EmptyNextLenInput.form B.allocation.extra tracker.global runtime parentTag first fresh room
    ∃nextData,∃Q : UniformWindow post next nextData owner id offset 1 .ret,
      Q.pointer=B.pointer ∧Q.loan=B.loan ∧Q.allocation=B.allocation.setExtra second.after ∧
      Q.precise.completion=CurrentCallZeroSharedBoolWindow.completion B.allocation.extra B.precise.completion parentTag tracker.global.nextPointerTag first
        tracker.global.nextPointerTag (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh) second ∧
      PointerBinds Q.allocation original ∧SpatialDelegation post next id Q.allocation Q.precise.completion original.grant := by
  dsimp only
  let second:=S03EmptyNextLenInput.form B.allocation.extra tracker.global runtime parentTag first fresh room
  have growth : EmptyForestSharedPoolNext.growth first≤1 := by cases selected:first.slot <;> simp [EmptyForestSharedPoolNext.growth,selected]
  have size:=EmptyForestSharedPoolNext.node_size first
  have firstBound : tracker.global.nextPointerTag.value.toNat<next.global.nextPointerTag.value.toNat := by omega
  have secondBound : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat<next.global.nextPointerTag.value.toNat := by
    rw [GenericFunctionEntryNumerics.successor_value]
    omega
  have firstOrder : first.parentNode.tag.value≤tracker.global.nextPointerTag.value := by
    have older:=GeneralBorrowForestTagHighWater.mapped B.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag first.parentNode.tag
      runtime.below first.parent (runtime.formed.allocator.nodeTags first.parent first.parentNode first.present)
    exact UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt older)
  have secondTag : second.parentNode.tag=tracker.global.nextPointerTag := by
    obtain ⟨node,nodeAt,tagEq,_,_,_,_⟩:=GeneralBorrowFreshMetadataChildSifa.node_fields first.stage first.parent .Read first.index
      (GeneralBorrowFreshAnchor.sharedNode tracker.global.nextPointerTag first.parent) first.stage_new
    have secondParent : second.parent=first.index:=rfl
    have same : node=second.parentNode:=Option.some.inj (nodeAt.symm.trans (by rw [←secondParent];exact second.present))
    rw [←same]
    exact tagEq
  have secondOrder : second.parentNode.tag.value≤(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value := by
    rw [secondTag]
    apply UInt64.le_iff_toNat_le.mpr
    rw [GenericFunctionEntryNumerics.successor_value]
    omega
  obtain ⟨nextData,Q,pointer,loan,allocation,completion⟩:=CurrentCallZeroSharedBoolWindow.window_two B next parentTag tracker.global.nextPointerTag first tracker.global.nextPointerTag
    (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh) second runtime (by rw [globalShape]) (by omega)
    (by omega) firstBound (by omega) secondBound firstOrder secondOrder post present (by rw [globalShape];rfl) start startEq
  refine ⟨nextData,Q,pointer,loan,allocation,completion,?_,?_⟩
  · rw [allocation]
    exact CurrentCallZeroSharedBoolWindow.binding_two B next parentTag tracker.global.nextPointerTag first tracker.global.nextPointerTag
      (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh) second runtime (by rw [globalShape]) (by omega)
      (by omega) firstBound (by omega) secondBound firstOrder secondOrder original oldBinding
  · rw [allocation,completion]
    exact CurrentCallZeroSharedBoolWindow.license_two B next parentTag tracker.global.nextPointerTag first tracker.global.nextPointerTag
      (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh) second runtime (by rw [globalShape]) (by omega)
      (by omega) firstBound (by omega) secondBound firstOrder secondOrder post present (by rw [globalShape];rfl) oldIssued
end
end DuplicatePrefix.CurrentCallEmptyLiveHelperCurrent
