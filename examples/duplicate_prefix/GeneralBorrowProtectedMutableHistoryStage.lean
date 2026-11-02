import duplicate_prefix.GeneralBorrowProtectedChildComplete
import duplicate_prefix.GeneralBorrowProtectedConstructorState
import duplicate_prefix.GeneralBorrowProtectedMutableLifecycle

namespace DuplicatePrefix.GeneralBorrowProtectedMutableHistoryStage
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Actual fresh Strong registration, root Read, protected Default reservation,
child Write, source release and real endCall form another full recurring root
State. The State projections during the protected lifetime are counterfactual
unheld data; actual root Write ownership is asserted after actual endCall only. -/
theorem borrow (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295)
    (global : GlobalState) (empty : global.protectedTags = {}) (allocation : AllocId) :
    (GeneralBorrowProtectedMutableStage.read tree s.node.tag tag offset len global allocation).status = .Completed ∧
    (GeneralBorrowProtectedMutableStage.child tree s.node.tag tag offset len global allocation).outcome = .ok () ∧
    (GeneralBorrowProtectedMutableLifecycle.write tree s.node.tag tag offset len global allocation).status = .Completed ∧
    (GeneralBorrowProtectedMutableLifecycle.released tree s.node.tag tag offset len global allocation).status = .Released ∧
    ((GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.endCall
      (GeneralBorrowProtectedMutableRelease.registration global allocation tag).2).protectedTags = {} ∧
    Nonempty {post : State (GeneralBorrowProtectedMutableLifecycle.released tree s.node.tag tag offset len global allocation).tree root capacity // post.node.tag = s.node.tag} ∧
    (GeneralBorrowProtectedMutableLifecycle.released tree s.node.tag tag offset len global allocation).tree.nodes.size ≤ tree.nodes.size+1 ∧
    (∀ future, tag ≠ future → GeneralBorrowTagMap.Fresh tree.tagMapping future →
      GeneralBorrowTagMap.Fresh (GeneralBorrowProtectedMutableLifecycle.released tree s.node.tag tag offset len global allocation).tree.tagMapping future) := by
  have heldEq : (GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.protectedTags = ({} : ProtectedTags).insert tag .StrongProtector := by
    simp [GeneralBorrowProtectedMutableRelease.registration,GlobalState.addProtector,empty]
  have readEq : GeneralBorrowProtectedMutableStage.read tree s.node.tag tag offset len global allocation =
      GeneralBorrowProtectedRootRead.operation tree s.node.tag offset len tag := by
    simp only [GeneralBorrowProtectedMutableStage.read,GeneralBorrowProtectedRootRead.operation,BorrowTree.performNormalAccessRange,heldEq]
  have readResult := GeneralBorrowProtectedRootRead.read tree root capacity s offset len tag fresh bounds
  rw [←readEq] at readResult
  obtain ⟨⟨afterRead,readTag⟩⟩ := readResult.2.1
  let accessed := (GeneralBorrowProtectedMutableStage.read tree s.node.tag tag offset len global allocation).tree
  have freshRead : GeneralBorrowTagMap.Fresh accessed.tagMapping tag := by rw [readResult.2.2.2];exact fresh
  have roomRead : accessed.nodes.size+5 ≤ 4294967295 := by rw [readResult.2.2.1];exact room
  have reserved := GeneralBorrowPartitionProtectedDefault.reserve accessed root capacity afterRead offset len nonzero bounds tag freshRead roomRead
  have prepared := GeneralBorrowProtectedConstructorState.prepare accessed root capacity afterRead offset len nonzero bounds tag freshRead roomRead
  have treeEq : GeneralBorrowProtectedConstructorState.reserved accessed afterRead.node.tag tag offset len =
      (GeneralBorrowProtectedMutableStage.child tree s.node.tag tag offset len global allocation).tree := by
    rw [readTag]
    rfl
  have operationEq : GeneralBorrowPartitionProtectedDefault.operation accessed afterRead.node.tag tag offset len =
      GeneralBorrowProtectedMutableStage.child tree s.node.tag tag offset len global allocation := by
    rw [readTag]
    rfl
  rw [operationEq] at reserved
  rw [treeEq] at prepared
  obtain ⟨reservedOK,before,index,node,rootTag,lookup,present,tagged,parent,typed⟩ := prepared
  obtain ⟨readDone,childDone,⟨data⟩⟩ := GeneralBorrowProtectedMutableStage.prepare tree root capacity s offset len nonzero bounds tag fresh global empty allocation
  have sameIndex : index = data.index := Option.some.inj (lookup.symm.trans data.lookup)
  subst index
  have finished := GeneralBorrowProtectedChildComplete.complete (GeneralBorrowProtectedMutableStage.child tree s.node.tag tag offset len global allocation).tree root data.index capacity
    before data.node data.present data.parent data.unexposed tag data.lookup typed offset len nonzero bounds data.active global empty allocation
  obtain ⟨writeDone,releaseDone,endDone,⟨post,postTag⟩,nodes,mapping⟩ := finished
  refine ⟨readDone,childDone,writeDone,releaseDone,endDone,⟨⟨post,postTag.trans (rootTag.trans readTag)⟩⟩,?_,?_⟩
  · change (GeneralBorrowProtectedMutableRelease.release _ tag offset len _).tree.nodes.size ≤ _
    rw [nodes]
    have growth := reserved.2.2.1
    rw [readResult.2.2.1] at growth
    exact growth
  · intro future different oldFresh
    change GeneralBorrowTagMap.Fresh (GeneralBorrowProtectedMutableRelease.release _ tag offset len _).tree.tagMapping future
    rw [mapping]
    apply reserved.2.2.2 future different
    rw [readResult.2.2.2]
    exact oldFresh
end
end DuplicatePrefix.GeneralBorrowProtectedMutableHistoryStage
