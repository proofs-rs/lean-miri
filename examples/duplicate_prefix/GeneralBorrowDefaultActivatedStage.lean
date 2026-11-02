import duplicate_prefix.GeneralBorrowDefaultChildState

namespace DuplicatePrefix.GeneralBorrowDefaultActivatedStage
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Exact Unique establishment at each real per-location child Write callback.
The actual ranged operation invokes this callback only on requested intervals;
untouched outside intervals are not claimed to become Unique. -/
theorem normal_unique (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295) :
    ∃ index, (GeneralBorrowDefaultActivation.reserved tree s.node.tag tag offset len).indexOfTag tag = some index ∧
      ∀ position (valid : position < (GeneralBorrowDefaultActivation.reserved tree s.node.tag tag offset len).locations.entries.size),
        ∃ state,
          ((GeneralBorrowDefaultActivation.reserved tree s.node.tag tag offset len).performNormalAccessAt
            (GeneralBorrowDefaultActivation.reserved tree s.node.tag tag offset len).locations.entries[position].data
            index .Write {} .VisitChildrenOfAccessed).location.perms.get index = some state ∧ state.permission = .Unique := by
  obtain ⟨formed,before,index,node,rootTag,lookup,present,tagged,parent,typed⟩ :=
    GeneralBorrowDefaultChildState.prepare tree root capacity s offset len nonzero bounds tag fresh room
  have all := GeneralBorrowDefaultChildState.child_every _ root index capacity before node present parent typed
  refine ⟨index,lookup,?_⟩
  intro position valid
  have owned := all position valid
  obtain ⟨forest⟩ := owned.1
  apply GeneralBorrowWriteActivationUnique.normal _ _ {} index .VisitChildrenOfAccessed forest owned.2
  intro state found
  have permission := GeneralBorrowDefaultReservationType.effective _ _ index node present typed.1 (typed.2 position valid) state found
  rw [permission]
  decide

/-- Full actual root Read, reservation, and child-tag Write. -/
def operation (tree : BorrowTree) (parentTag tag : BorTag) (offset len : UInt64) :=
  GeneralBorrowDefaultActivation.stageWrite tree parentTag tag offset len

/-- The actual Read→reservation→child Write stage re-establishes the ROOT
recurring contract and consumes one fresh tag, with actual append/reuse selected
internally. It can be inserted into finite root histories without supplying any
intermediate state, ownership, successful operation or lifetime-restoration fact. -/
theorem borrow (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295) :
    (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).status = .Completed ∧
    (GeneralBorrowPartitionDefaultStage.operation tree s.node.tag tag offset len).outcome = .ok () ∧
    (operation tree s.node.tag tag offset len).status = .Completed ∧
    Nonempty {post : State (operation tree s.node.tag tag offset len).tree root capacity // post.node.tag = s.node.tag} ∧
    (operation tree s.node.tag tag offset len).tree.nodes.size ≤ tree.nodes.size+1 ∧
    (∀ future, tag ≠ future → GeneralBorrowTagMap.Fresh tree.tagMapping future →
      GeneralBorrowTagMap.Fresh (operation tree s.node.tag tag offset len).tree.tagMapping future) := by
  have read := GeneralBorrowPartitionState.access tree root capacity s offset len .Read bounds
  obtain ⟨⟨prepared,preparedTag⟩⟩ := read.2.1
  have nextFresh : GeneralBorrowTagMap.Fresh (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).tree.tagMapping tag := by
    rw [read.2.2.2];exact fresh
  have nextRoom : (GeneralBorrowPartitionState.operation tree s.node.tag offset len .Read).tree.nodes.size+5 ≤ 4294967295 := by
    rw [read.2.2.1];exact room
  have activated := GeneralBorrowDefaultChildState.activate _ root capacity prepared offset len nonzero bounds tag nextFresh nextRoom
  rw [preparedTag] at activated
  have reserved := GeneralBorrowPartitionDefault.reserve _ root capacity prepared offset len nonzero bounds tag nextFresh nextRoom
  rw [preparedTag] at reserved
  let child := GeneralBorrowPartitionDefaultStage.operation tree s.node.tag tag offset len
  let final := operation tree s.node.tag tag offset len
  have frame := GeneralBorrowFreshReadFrame.frame child.tree (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) .Write {} .VisitChildrenOfAccessed
  have nodes : final.tree.nodes = child.tree.nodes := by
    simpa only [final,operation,GeneralBorrowDefaultActivation.stageWrite,BorrowTree.performNormalAccessRange,child] using congrArg BorrowTree.nodes frame
  have mapping : final.tree.tagMapping = child.tree.tagMapping := by
    simpa only [final,operation,GeneralBorrowDefaultActivation.stageWrite,BorrowTree.performNormalAccessRange,child] using congrArg BorrowTree.tagMapping frame
  refine ⟨read.1,activated.1,activated.2.1,activated.2.2,?_,?_⟩
  · have bound : child.tree.nodes.size ≤ tree.nodes.size+1 := by
      have bound := reserved.2.2.1
      rw [read.2.2.1] at bound
      exact bound
    rw [show (operation tree s.node.tag tag offset len).tree.nodes = child.tree.nodes from nodes]
    exact bound
  · intro future different unused
    rw [show (operation tree s.node.tag tag offset len).tree.tagMapping = child.tree.tagMapping from mapping]
    exact reserved.2.2.2 future different (by rw [read.2.2.2];exact unused)
end
end DuplicatePrefix.GeneralBorrowDefaultActivatedStage
