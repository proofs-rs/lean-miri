import duplicate_prefix.GeneralBorrowRawAsMutToCopy
import duplicate_prefix.GeneralBorrowRawCopyInput
import duplicate_prefix.GeneralBorrowFreshParentTagOrder
namespace DuplicatePrefix.GeneralBorrowRawAsMutCopyResources
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
/-- The real mutable helper release produces the entire semantic copy packet,
including conditional graph order and resource bounds, from current helper
resources. No post-release permissions or successful copy is a premise. -/
theorem copy_input (input : GeneralBorrowRawAsMutToCopy.Input) :
    let released := (input.entry.allocation.extra.releaseProtector input.tag input.tracker.global.protectedTags).tree
    let held := GeneralBorrowRawAsMutToCopy.held input
    ∃ borrow : GeneralBorrowRawCopyInput.Input released held.global input.tag input.offset input.len input.count,
      borrow.anchor = input.anchor ∧ borrow.selected = input.selected ∧ borrow.maximum = input.maximum := by
  obtain ⟨_,afterRuntime,⟨afterPositive⟩,_,_,_,shape,_⟩ :=
    GeneralBorrowBothProtectorReleaseEndCall.release_end_call input.entry.allocation.extra input.tracker.global input.runtime
      input.id input.tag input.anchor input.selected input.maximum input.offset input.len
      input.owner input.node input.nodePresent input.sameTag input.hidden input.tagged input.distinct input.order input.short input.activity
  let released := (input.entry.allocation.extra.releaseProtector input.tag input.tracker.global.protectedTags).tree
  have roots := congrArg BorrowTree.roots shape
  change released.roots = input.entry.allocation.extra.roots at roots
  have nodeFrame := congrArg BorrowTree.nodes shape
  change released.nodes = input.entry.allocation.extra.nodes at nodeFrame
  have nodes := congrArg (fun tree : BorrowTree => tree.nodes.size) shape
  change released.nodes.size = input.entry.allocation.extra.nodes.size at nodes
  have mapping := congrArg BorrowTree.tagMapping shape
  change released.tagMapping = input.entry.allocation.extra.tagMapping at mapping
  have twice : input.count.toNat+input.count.toNat ≤ input.len.toNat := by
    have within := UInt64.le_iff_toNat_le.mp input.within
    rw [UInt64.toNat_div] at within
    change input.count.toNat ≤ input.len.toNat/2 at within
    omega
  refine ⟨⟨input.anchor,input.selected,input.maximum,?_,afterPositive,afterRuntime,?_,?_,?_,twice⟩,rfl,rfl,rfl⟩
  · change released.tagMapping.get input.tag = some input.anchor
    rw [mapping]
    exact input.tagged
  · rw [roots]
    exact input.distinct
  · intro valid different
    have validOld : 0 < input.entry.allocation.extra.roots.size := by rw [←roots];exact valid
    have differentOld : input.selected ≠ input.entry.allocation.extra.roots[0] := by
      change input.selected ≠ released.roots[0] at different
      simpa only [roots] using different
    unfold GeneralBorrowWildcardParentTagOrder.ParentTagOrder
    rw [nodeFrame]
    exact input.order validOld differentOld
  · rw [nodes]
    exact input.short
end
end DuplicatePrefix.GeneralBorrowRawAsMutCopyResources
