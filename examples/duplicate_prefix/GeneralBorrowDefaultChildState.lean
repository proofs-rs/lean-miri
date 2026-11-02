import duplicate_prefix.GeneralBorrowDefaultActivation
import duplicate_prefix.GeneralBorrowRootChildWriteOwnership

namespace DuplicatePrefix.GeneralBorrowDefaultChildState
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Derive the actual reserved child, its parent edge, and exact reservation
typing alongside the recurring parent state. No poststate is an input premise. -/
theorem prepare (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295) :
    (GeneralBorrowPartitionDefault.operation tree s.node.tag tag offset len).outcome = .ok () ∧
    ∃ (post : State (GeneralBorrowDefaultActivation.reserved tree s.node.tag tag offset len) root capacity)
      (index : UniIndex) (node : TreeNode), post.node.tag = s.node.tag ∧
      (GeneralBorrowDefaultActivation.reserved tree s.node.tag tag offset len).indexOfTag tag = some index ∧
      (GeneralBorrowDefaultActivation.reserved tree s.node.tag tag offset len).nodeAt index = some node ∧
      node.tag = tag ∧ node.parent = some root ∧
      GeneralBorrowDefaultReservationType.TreeTyped (GeneralBorrowDefaultActivation.reserved tree s.node.tag tag offset len) index := by
  have reserved := GeneralBorrowPartitionDefault.reserve tree root capacity s offset len nonzero bounds tag fresh room
  obtain ⟨⟨post,postTag⟩⟩ := reserved.2.1
  let entry := GeneralBorrowPartitionEntryData.data tree root capacity s tag fresh
  let index := GeneralBorrowFreshMetadataChildDefaultSlot.index entry.slot
  have request : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat := by rw [s.capacity];exact bounds
  have clean : Every (fun location : LocationTree => location.perms.get index = none) tree.locations := by
    have vacant : tree.nodes.get index = none := by
      have empty := GeneralBorrowFreshDefaultStages.slot_vacant tree entry.depth root entry.slot
      cases chosen : entry.slot <;>
        simpa only [index,GeneralBorrowFreshMetadataChildDefaultSlot.index,GeneralBorrowFreshDefaultStages.slot_index,chosen] using empty
    exact s.clean index vacant
  have specific : ∃ node,
      (GeneralBorrowDefaultActivation.reserved tree s.node.tag tag offset len).indexOfTag tag = some index ∧
      (GeneralBorrowDefaultActivation.reserved tree s.node.tag tag offset len).nodeAt index = some node ∧
      node.tag = tag ∧ node.parent = some root ∧
      GeneralBorrowDefaultReservationType.TreeTyped (GeneralBorrowDefaultActivation.reserved tree s.node.tag tag offset len) index := by
    cases chosen : entry.slot with
    | append noFree aligned fits =>
      let input : GeneralBorrowFreshMetadataChildDefault.Input :=
        ⟨tree,entry.depth,entry.children,entry.covered,s.node.tag,tag,root,s.node,
          s.allocator.nodeTags root s.node s.star.present,s.star.present,fresh,noFree,aligned,fits,offset,len,nonzero,s.well,request⟩
      have metadata := GeneralBorrowFreshMetadataChildDefault.append input
      obtain ⟨node,present,tagged,parent,children,permission,exposed⟩ := metadata.newNode
      have typed := GeneralBorrowDefaultReservationType.Append.formed input (by
        simpa only [input,GeneralBorrowFreshMetadataChildDefault.index,index,GeneralBorrowFreshMetadataChildDefaultSlot.index,chosen] using clean)
      refine ⟨node,?_,?_,tagged,parent,?_⟩
      · simpa only [GeneralBorrowDefaultActivation.reserved,GeneralBorrowPartitionDefault.operation,GeneralBorrowFreshMetadataChildDefault.result,
          input,index,GeneralBorrowFreshMetadataChildDefault.index,GeneralBorrowFreshMetadataChildDefaultSlot.index,chosen] using metadata.freshLookup
      · simpa only [GeneralBorrowDefaultActivation.reserved,GeneralBorrowPartitionDefault.operation,GeneralBorrowFreshMetadataChildDefault.result,
          input,index,GeneralBorrowFreshMetadataChildDefault.index,GeneralBorrowFreshMetadataChildDefaultSlot.index,chosen] using present
      · simpa only [GeneralBorrowDefaultActivation.reserved,GeneralBorrowPartitionDefault.operation,GeneralBorrowFreshMetadataChildDefault.result,
          input,index,GeneralBorrowFreshMetadataChildDefault.index,GeneralBorrowFreshMetadataChildDefaultSlot.index,chosen] using typed
    | reuse candidate available bounded vacant slack =>
      let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
        ⟨tree,entry.depth,entry.children,entry.covered,s.node.tag,tag,root,s.node,
          s.allocator.nodeTags root s.node s.star.present,s.star.present,fresh,candidate,available,bounded,vacant,slack,offset,len,nonzero,s.well,request⟩
      have metadata := GeneralBorrowFreshMetadataChildDefaultReuse.reuse input
      obtain ⟨node,present,tagged,parent,children,permission,exposed⟩ := metadata.newNode
      have typed := GeneralBorrowDefaultReservationType.Reuse.formed input (by
        simpa only [input,GeneralBorrowFreshMetadataChildDefaultReuse.index,index,GeneralBorrowFreshMetadataChildDefaultSlot.index,chosen] using clean)
      refine ⟨node,?_,?_,tagged,parent,?_⟩
      · simpa only [GeneralBorrowDefaultActivation.reserved,GeneralBorrowPartitionDefault.operation,GeneralBorrowFreshMetadataChildDefaultReuse.result,
          input,index,GeneralBorrowFreshMetadataChildDefaultReuse.index,GeneralBorrowFreshMetadataChildDefaultSlot.index,chosen] using metadata.freshLookup
      · simpa only [GeneralBorrowDefaultActivation.reserved,GeneralBorrowPartitionDefault.operation,GeneralBorrowFreshMetadataChildDefaultReuse.result,
          input,index,GeneralBorrowFreshMetadataChildDefaultReuse.index,GeneralBorrowFreshMetadataChildDefaultSlot.index,chosen] using present
      · simpa only [GeneralBorrowDefaultActivation.reserved,GeneralBorrowPartitionDefault.operation,GeneralBorrowFreshMetadataChildDefaultReuse.result,
          input,index,GeneralBorrowFreshMetadataChildDefaultReuse.index,GeneralBorrowFreshMetadataChildDefaultSlot.index,chosen] using typed
  obtain ⟨node,lookup,present,tagged,parent,typed⟩ := specific
  exact ⟨reserved.1,post,index,node,postTag,lookup,present,tagged,parent,typed⟩

/-- The reservation's real lazy outside state is locally writable too. Hence
child ownership is available on every stored interval, not just its created range. -/
theorem child_every (tree : BorrowTree) (root child : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (node : TreeNode) (present : tree.nodeAt child = some node)
    (parent : node.parent = some root) (typed : GeneralBorrowDefaultReservationType.TreeTyped tree child) :
    Every (GeneralBorrowRange.LocationOwned tree {} child .Write) tree.locations := by
  intro position valid
  have rootOwned := s.owned position valid
  refine ⟨rootOwned.1,?_⟩
  apply GeneralBorrowRootChildWriteOwnership.child_of_root tree _ root child s.node node
    s.star.present s.star.parentless present parent rootOwned.2
  exact GeneralBorrowDefaultReservationType.effective tree _ child node present typed.1 (typed.2 position valid)

/-- Actual child-tag Write after an actual Default reservation re-establishes
the ROOT recurring State. Root ownership is recovered from the proved child
Write ownership and ancestor relation, not assumed to survive the operation. -/
theorem activate (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295) :
    (GeneralBorrowPartitionDefault.operation tree s.node.tag tag offset len).outcome = .ok () ∧
    (GeneralBorrowDefaultActivation.write tree s.node.tag tag offset len).status = .Completed ∧
    Nonempty {post : State (GeneralBorrowDefaultActivation.write tree s.node.tag tag offset len).tree root capacity // post.node.tag = s.node.tag} := by
  obtain ⟨formed,before,index,node,rootTag,lookup,present,tagged,parent,typed⟩ :=
    prepare tree root capacity s offset len nonzero bounds tag fresh room
  let reserved := GeneralBorrowDefaultActivation.reserved tree s.node.tag tag offset len
  let result := GeneralBorrowDefaultActivation.write tree s.node.tag tag offset len
  let depth := GeneralBorrowStarCertificates.depth reserved root before.node before.star
  have children := GeneralBorrowStarCertificates.children reserved root before.node before.star
  have covered := GeneralBorrowStarCertificates.covered reserved root before.node before.star before.roots
  have fits : reserved.nodes.data.size ≤ 4294967296 := by have bound := before.room;change reserved.nodes.data.size+4 ≤ _ at bound;omega
  have request : (Size.ofBytes offset).bytes.toNat+(Size.ofBytes len).bytes.toNat ≤ reserved.locations.size.bytes.toNat := by rw [before.capacity];exact bounds
  have allChildren := child_every reserved root index capacity before node present parent typed
  have facts := GeneralBorrowRangePreserves.ranged reserved {} tag index root (Size.ofBytes offset) (Size.ofBytes len)
    .Write .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) fits depth children node present before.roots covered lookup before.well allChildren request
  let predicate := fun location : LocationTree => ∀ query, reserved.nodes.get query = none → location.perms.get query = none
  have clean : Every predicate reserved.locations := by
    intro position valid query vacant
    exact before.clean query vacant position valid
  have preserved := GeneralBorrowRangeProperty.preserves predicate reserved {} tag index root (Size.ofBytes offset) (Size.ofBytes len)
    .Write .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) fits depth children node present before.roots covered lookup before.well allChildren clean (by
      intro location good owned query vacant
      exact GeneralBorrowFreshActiveOnClean.normal_vacant reserved location {} index query .Write .VisitChildrenOfAccessed
        depth children node present vacant (good query vacant)) request
  have frame := GeneralBorrowFreshReadFrame.frame reserved (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) .Write {} .VisitChildrenOfAccessed
  have nodes : result.tree.nodes = reserved.nodes := by simpa only [result,GeneralBorrowDefaultActivation.write,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.nodes frame
  have mapping : result.tree.tagMapping = reserved.tagMapping := by simpa only [result,GeneralBorrowDefaultActivation.write,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.tagMapping frame
  have roots : result.tree.roots = reserved.roots := by simpa only [result,GeneralBorrowDefaultActivation.write,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.roots frame
  have star := GeneralBorrowGeneratedStarShape.of_nodes reserved result.tree root before.node nodes before.star
  have childPresent : result.tree.nodeAt index = some node := by change result.tree.nodes.get index = some node;rw [nodes];exact present
  have owners : Every (GeneralBorrowRange.LocationOwned result.tree {} root .Write) result.tree.locations := by
    intro position valid
    have childOwned := facts.2.1 position valid
    refine ⟨childOwned.1,?_⟩
    exact GeneralBorrowRootChildWriteOwnership.root_of_child result.tree _ root index before.node node
      star.present star.parentless childPresent parent childOwned.2
  have nextClean : GeneralBorrowGcVacantClean.VacantClean result.tree := by
    intro query vacant position valid
    rw [nodes] at vacant
    exact preserved.2.1 position valid query vacant
  refine ⟨formed,facts.1,⟨⟨⟨before.node,before.nonzero,star,roots.trans before.roots,
    facts.2.2.2.trans before.capacity,facts.2.2.1,owners,?_,nextClean,?_⟩,rootTag⟩⟩⟩
  · constructor
    · rw [nodes,mapping];exact before.allocator.pool
    · unfold GeneralBorrowFreshStagePool.Accounting
      rw [nodes,mapping];exact before.allocator.accounting
    · rw [mapping];exact before.allocator.unique
    · intro query value found
      rw [nodes] at found
      rw [mapping]
      exact before.allocator.nodeTags query value found
  · rw [nodes];exact before.room
end
end DuplicatePrefix.GeneralBorrowDefaultChildState
