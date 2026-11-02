import duplicate_prefix.GeneralBorrowPartitionProtectedDefault
import duplicate_prefix.GeneralBorrowPartitionEntryData
import duplicate_prefix.GeneralBorrowFreshMutableStages
import duplicate_prefix.GeneralBorrowProtectedReservationType
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableSlot
namespace DuplicatePrefix.GeneralBorrowProtectedConstructorState
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

def reserved (tree : BorrowTree) (parentTag tag : BorTag) (offset len : UInt64) :=
  (GeneralBorrowPartitionProtectedDefault.operation tree parentTag tag offset len).tree

/-- Exact actual protected reservation, with counterfactual unheld root State
and reserved child typing; actual registered root permission is not claimed. -/
theorem prepare (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295) :
    (GeneralBorrowPartitionProtectedDefault.operation tree s.node.tag tag offset len).outcome = .ok () ∧
    ∃ (post : State (reserved tree s.node.tag tag offset len) root capacity)
      (index : UniIndex) (node : TreeNode), post.node.tag = s.node.tag ∧
      (reserved tree s.node.tag tag offset len).indexOfTag tag = some index ∧
      (reserved tree s.node.tag tag offset len).nodeAt index = some node ∧
      node.tag = tag ∧ node.parent = some root ∧
      GeneralBorrowDefaultReservationType.TreeTyped (reserved tree s.node.tag tag offset len) index := by
  have formed := GeneralBorrowPartitionProtectedDefault.reserve tree root capacity s offset len nonzero bounds tag fresh room
  obtain ⟨⟨post,postTag⟩⟩ := formed.2.1
  let entry := GeneralBorrowPartitionEntryData.data tree root capacity s tag fresh
  let index := GeneralBorrowFreshMetadataChildMutableSlot.index entry.slot
  have request : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat := by rw [s.capacity];exact bounds
  have clean : Every (fun location : LocationTree => location.perms.get index = none) tree.locations := by
    have vacant : tree.nodes.get index = none := by
      have empty := GeneralBorrowFreshMutableStages.slot_vacant tree entry.depth root entry.slot
      cases chosen : entry.slot <;>
        simpa only [index,GeneralBorrowFreshMetadataChildMutableSlot.index,GeneralBorrowFreshMutableStages.slot_index,chosen] using empty
    exact s.clean index vacant
  have specific : ∃ node,
      (reserved tree s.node.tag tag offset len).indexOfTag tag = some index ∧
      (reserved tree s.node.tag tag offset len).nodeAt index = some node ∧
      node.tag = tag ∧ node.parent = some root ∧
      GeneralBorrowDefaultReservationType.TreeTyped (reserved tree s.node.tag tag offset len) index := by
    cases chosen : entry.slot with
    | append noFree aligned fits =>
      let input : GeneralBorrowFreshMetadataChildMutable.Input :=
        ⟨tree,entry.depth,entry.children,entry.covered,s.node.tag,tag,root,s.node,
          s.allocator.nodeTags root s.node s.star.present,s.star.present,fresh,noFree,aligned,fits,offset,len,nonzero,s.well,request⟩
      have metadata := GeneralBorrowFreshMetadataChildMutable.append input
      obtain ⟨node,present,tagged,parent,children,permission,exposed⟩ := metadata.newNode
      have typed := GeneralBorrowProtectedReservationType.Append.formed input (by
        simpa only [input,GeneralBorrowFreshMetadataChildMutable.index,index,GeneralBorrowFreshMetadataChildMutableSlot.index,chosen] using clean)
      refine ⟨node,?_,?_,tagged,parent,?_⟩
      · simpa only [reserved,GeneralBorrowPartitionProtectedDefault.operation,GeneralBorrowFreshMetadataChildMutable.result,
          input,index,GeneralBorrowFreshMetadataChildMutable.index,GeneralBorrowFreshMetadataChildMutableSlot.index,chosen] using metadata.freshLookup
      · simpa only [reserved,GeneralBorrowPartitionProtectedDefault.operation,GeneralBorrowFreshMetadataChildMutable.result,
          input,index,GeneralBorrowFreshMetadataChildMutable.index,GeneralBorrowFreshMetadataChildMutableSlot.index,chosen] using present
      · simpa only [reserved,GeneralBorrowPartitionProtectedDefault.operation,GeneralBorrowFreshMetadataChildMutable.result,
          input,index,GeneralBorrowFreshMetadataChildMutable.index,GeneralBorrowFreshMetadataChildMutableSlot.index,chosen] using typed
    | reuse candidate available bounded vacant slack =>
      let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
        ⟨tree,entry.depth,entry.children,entry.covered,s.node.tag,tag,root,s.node,
          s.allocator.nodeTags root s.node s.star.present,s.star.present,fresh,candidate,available,bounded,vacant,slack,offset,len,nonzero,s.well,request⟩
      have metadata := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
      obtain ⟨node,present,tagged,parent,children,permission,exposed⟩ := metadata.newNode
      have typed := GeneralBorrowProtectedReservationType.Reuse.formed input (by
        simpa only [input,GeneralBorrowFreshMetadataChildMutableReuse.index,index,GeneralBorrowFreshMetadataChildMutableSlot.index,chosen] using clean)
      refine ⟨node,?_,?_,tagged,parent,?_⟩
      · simpa only [reserved,GeneralBorrowPartitionProtectedDefault.operation,GeneralBorrowFreshMetadataChildMutableReuse.result,
          input,index,GeneralBorrowFreshMetadataChildMutableReuse.index,GeneralBorrowFreshMetadataChildMutableSlot.index,chosen] using metadata.freshLookup
      · simpa only [reserved,GeneralBorrowPartitionProtectedDefault.operation,GeneralBorrowFreshMetadataChildMutableReuse.result,
          input,index,GeneralBorrowFreshMetadataChildMutableReuse.index,GeneralBorrowFreshMetadataChildMutableSlot.index,chosen] using present
      · simpa only [reserved,GeneralBorrowPartitionProtectedDefault.operation,GeneralBorrowFreshMetadataChildMutableReuse.result,
          input,index,GeneralBorrowFreshMetadataChildMutableReuse.index,GeneralBorrowFreshMetadataChildMutableSlot.index,chosen] using typed
  obtain ⟨node,lookup,present,tagged,parent,typed⟩ := specific
  exact ⟨formed.1,post,index,node,postTag,lookup,present,tagged,parent,typed⟩


end
end DuplicatePrefix.GeneralBorrowProtectedConstructorState
