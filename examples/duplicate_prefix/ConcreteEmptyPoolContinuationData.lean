import duplicate_prefix.ConcreteEmptyPoolEntryNext
import duplicate_prefix.EmptyForestSharedPoolReleaseFrame
import duplicate_prefix.EmptyForestSharedReleaseData

namespace DuplicatePrefix.ConcreteEmptyPoolContinuationData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert

/-- Raw initial history/allocator resources for CONCRETE parent FnEntry followed by
the real shared and len references. Every vacant permission is independently
Clean; noFree is NOT required. -/
structure Input (tree : BorrowTree) (parentTag rootTag sharedTag lenTag : BorTag) where
  parent : UniIndex
  parentNode : TreeNode
  tagged : tree.indexOfTag parentTag = some parent
  present : tree.nodeAt parent = some parentNode
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
variable {tree : BorrowTree} {parentTag rootTag sharedTag lenTag : BorTag}
def entry (input : Input tree parentTag rootTag sharedTag lenTag) : ConcreteEmptyPoolEntry.Input tree parentTag rootTag :=
  ConcreteEmptyPoolEntry.factory tree parentTag rootTag input.parent input.parentNode input.depth input.tagged input.present
    input.rootFresh input.pool input.accounting (by
      have balance := input.accounting
      unfold GeneralBorrowFreshStagePool.Accounting at balance
      have room := input.room
      omega) input.clean
def roots (input : Input tree parentTag rootTag sharedTag lenTag) : BorrowTree := input.entry.after

noncomputable def node (input : Input tree parentTag rootTag sharedTag lenTag) : TreeNode := Classical.choose input.entry.node_exists
theorem root_present (input : Input tree parentTag rootTag sharedTag lenTag) :
    input.roots.nodeAt input.entry.index = some input.node := (Classical.choose_spec input.entry.node_exists).1
theorem root_unexposed (input : Input tree parentTag rootTag sharedTag lenTag) : input.node.isExposed = false :=
  (Classical.choose_spec input.entry.node_exists).2
theorem root_tagged (input : Input tree parentTag rootTag sharedTag lenTag) : input.roots.indexOfTag rootTag = some input.entry.index := by
  unfold BorrowTree.indexOfTag
  change input.entry.after.tagMapping.get rootTag = some input.entry.index
  rw [input.entry.mapping_after]
  exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping rootTag input.rootFresh input.entry.index input.entry.free
theorem root_clean (input : Input tree parentTag rootTag sharedTag lenTag) :
    GeneralBorrowFreshFutureClean.Clean input.roots input.entry.index := input.entry.future_clean input.entry.index input.entry.clean

theorem room_after (input : Input tree parentTag rootTag sharedTag lenTag) : input.roots.nodes.size+1 ≤ 4294967295 := by
  have size := ConcreteEmptyPoolEntryNext.node_size input.entry
  have growth : ConcreteEmptyPoolEntryNext.growth input.entry ≤ 1 := by
    cases selected : input.entry.slot <;> simp [ConcreteEmptyPoolEntryNext.growth,selected]
  have room := input.room
  change input.entry.after.nodes.size+1 ≤ _
  omega

theorem fresh_after (input : Input tree parentTag rootTag sharedTag lenTag) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (different : rootTag ≠ tag) :
    GeneralBorrowTagMap.Fresh input.roots.tagMapping tag := by
  rw [show input.roots.tagMapping = input.entry.mapping from input.entry.mapping_after]
  intro row member
  rcases Array.mem_push.mp member with old | last
  · exact fresh row old
  · cases last;exact different

/-- The first concrete shared Input is formed from the actual new concrete
child, after either allocator branch. No post-state ownership/data is assumed. -/
noncomputable def first (input : Input tree parentTag rootTag sharedTag lenTag) :
    EmptyForestSharedPool.Input input.roots rootTag sharedTag :=
  ConcreteEmptyPoolEntryNext.next input.entry sharedTag input.pool input.accounting input.clean input.sharedFresh input.rootShared
    (by have := input.room;omega)

/-- The second shared len-reference Input uses the real residual free pool;
canonical depth and separate vacant Clean are reconstructed internally. -/
noncomputable def second (input : Input tree parentTag rootTag sharedTag lenTag) :
    EmptyForestSharedPool.Input input.first.after sharedTag lenTag := by
  have allocated := ConcreteEmptyPoolEntryNext.allocator input.entry input.pool input.accounting
  exact EmptyForestSharedPoolNext.next input.first lenTag allocated.1 allocated.2
    (ConcreteEmptyPoolEntryNext.vacant_clean input.entry input.clean) (input.fresh_after lenTag input.lenFresh input.rootLen)
    input.sharedLen input.room_after

/-- Old ROOT release metadata after the ACTUAL first shared constructor, for
either entry/shared allocator branch. Permission absence is transported from
the explicit initial vacant Clean invariant. -/
noncomputable def root (input : Input tree parentTag rootTag sharedTag lenTag) :
    EmptyForestSharedReleaseData.Data input.first.after rootTag := by
  have old := EmptyForestSharedPoolReleaseFrame.old_node input.first input.entry.index
    input.node input.root_present
  let node := Classical.choose old
  have present : input.first.after.nodeAt input.entry.index = some node := (Classical.choose_spec old).1
  have unexposed : node.isExposed = false := (Classical.choose_spec old).2.trans input.root_unexposed
  refine ⟨input.entry.index,node,?_,present,unexposed,input.first.future_clean input.entry.index input.root_clean⟩
  unfold BorrowTree.indexOfTag
  rw [input.first.mapping_after]
  exact (GeneralBorrowTagMap.pushed_get_old input.roots.tagMapping sharedTag rootTag (Ne.symm input.rootShared)
    input.first.index input.first.free).trans input.root_tagged

end Input
end DuplicatePrefix.ConcreteEmptyPoolContinuationData
