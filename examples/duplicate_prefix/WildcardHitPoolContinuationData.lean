import duplicate_prefix.WildcardHitPoolRoot
import duplicate_prefix.EmptyForestSharedPoolReleaseFrame
import duplicate_prefix.EmptyForestSharedReleaseData

namespace DuplicatePrefix.WildcardHitPoolContinuationData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

/-- Raw initial history/allocator resources for wildcard FnEntry followed by
the real shared and len references. Every vacant permission is independently
Clean; noFree is NOT required. -/
structure Input (tree : BorrowTree) (rootTag sharedTag lenTag : BorTag) where
  depth : GeneralBorrowExposure.ParentDepth tree.nodes
  pool : GeneralBorrowFreshAllocatorInvariant.Pool tree.nodes tree.tagMapping.deassigned
  accounting : GeneralBorrowFreshStagePool.Accounting tree
  clean : GeneralBorrowGcVacantClean.VacantClean tree
  rootFresh : GeneralBorrowTagMap.Fresh tree.tagMapping rootTag
  sharedFresh : GeneralBorrowTagMap.Fresh tree.tagMapping sharedTag
  lenFresh : GeneralBorrowTagMap.Fresh tree.tagMapping lenTag
  rootShared : rootTag ≠ sharedTag
  rootLen : rootTag ≠ lenTag
  sharedLen : sharedTag ≠ lenTag
  room : tree.nodes.size+2 ≤ 4294967295

namespace Input
variable {tree : BorrowTree} {rootTag sharedTag lenTag : BorTag}
def slot (input : Input tree rootTag sharedTag lenTag) : WildcardHitPoolRoot.Slot tree :=
  WildcardHitPoolRoot.factory tree input.pool input.accounting (by
    have balance := input.accounting
    unfold GeneralBorrowFreshStagePool.Accounting at balance
    have room := input.room
    omega)
def roots (input : Input tree rootTag sharedTag lenTag) : BorrowTree := input.slot.after rootTag

theorem root_present (input : Input tree rootTag sharedTag lenTag) :
    input.roots.nodeAt input.slot.index = some (WildcardHitZeroConstructor.rootNode rootTag (.ReservedFrz false) .None) :=
  GeneralBorrowFreshLocation.get_same tree.nodes input.slot.index _

theorem root_tagged (input : Input tree rootTag sharedTag lenTag) :
    input.roots.indexOfTag rootTag = some input.slot.index :=
  GeneralBorrowTagMap.pushed_get_new tree.tagMapping rootTag input.rootFresh input.slot.index input.slot.free

theorem root_clean (input : Input tree rootTag sharedTag lenTag) :
    GeneralBorrowFreshFutureClean.Clean input.roots input.slot.index := input.clean input.slot.index input.slot.vacant

theorem room_after (input : Input tree rootTag sharedTag lenTag) : input.roots.nodes.size+1 ≤ 4294967295 := by
  have size := input.slot.size rootTag
  have growth : input.slot.growth ≤ 1 := by cases input.slot <;> simp [WildcardHitPoolRoot.Slot.growth]
  have room := input.room
  change (input.slot.after rootTag).nodes.size+1 ≤ _
  omega

theorem fresh_after (input : Input tree rootTag sharedTag lenTag) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (different : rootTag ≠ tag) :
    GeneralBorrowTagMap.Fresh input.roots.tagMapping tag := by
  intro row member
  rcases Array.mem_push.mp member with old | last
  · exact fresh row old
  · cases last;exact different

/-- The first concrete shared Input is formed from the actual new wildcard
root, after either allocator branch. No post-state ownership/data is assumed. -/
noncomputable def first (input : Input tree rootTag sharedTag lenTag) :
    EmptyForestSharedPool.Input input.roots rootTag sharedTag := by
  have allocated := input.slot.allocator rootTag input.pool input.accounting
  have fits : input.roots.tagMapping.mapping.size ≤ 4294967295 := by
    have accounting := allocated.2
    unfold GeneralBorrowFreshStagePool.Accounting at accounting
    have room := input.room_after
    change input.roots.tagMapping.mapping.size+input.roots.tagMapping.deassigned.size = input.roots.nodes.size at accounting
    omega
  exact EmptyForestSharedPool.factory input.roots rootTag sharedTag input.slot.index
    (WildcardHitZeroConstructor.rootNode rootTag (.ReservedFrz false) .None) (input.slot.depth input.depth rootTag)
    input.root_tagged input.root_present (input.fresh_after sharedTag input.sharedFresh input.rootShared)
    allocated.1 allocated.2 fits (input.slot.vacant_clean rootTag input.clean)

/-- The second shared len-reference Input uses the real residual free pool;
canonical depth and separate vacant Clean are reconstructed internally. -/
noncomputable def second (input : Input tree rootTag sharedTag lenTag) :
    EmptyForestSharedPool.Input input.first.after sharedTag lenTag := by
  have allocated := input.slot.allocator rootTag input.pool input.accounting
  exact EmptyForestSharedPoolNext.next input.first lenTag allocated.1 allocated.2
    (input.slot.vacant_clean rootTag input.clean) (input.fresh_after lenTag input.lenFresh input.rootLen)
    input.sharedLen input.room_after

/-- Old ROOT release metadata after the ACTUAL first shared constructor, for
either root/shared allocator branch. Permission absence is transported from
the explicit initial vacant Clean invariant. -/
noncomputable def root (input : Input tree rootTag sharedTag lenTag) :
    EmptyForestSharedReleaseData.Data input.first.after rootTag := by
  have old := EmptyForestSharedPoolReleaseFrame.old_node input.first input.slot.index
    (WildcardHitZeroConstructor.rootNode rootTag (.ReservedFrz false) .None) input.root_present
  let node := Classical.choose old
  have present : input.first.after.nodeAt input.slot.index = some node := (Classical.choose_spec old).1
  have unexposed : node.isExposed = false := (Classical.choose_spec old).2
  refine ⟨input.slot.index,node,?_,present,unexposed,input.first.future_clean input.slot.index input.root_clean⟩
  unfold BorrowTree.indexOfTag
  rw [input.first.mapping_after]
  exact (GeneralBorrowTagMap.pushed_get_old input.roots.tagMapping sharedTag rootTag (Ne.symm input.rootShared)
    input.first.index input.first.free).trans input.root_tagged

end Input
end DuplicatePrefix.WildcardHitPoolContinuationData
