import duplicate_prefix.GeneralBorrowProtectedMutableRelease
import duplicate_prefix.GeneralBorrowPartitionEntryData
import duplicate_prefix.GeneralBorrowGeneratedReuseStarShape
import duplicate_prefix.GeneralBorrowFreshMutableStages
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableSlot

namespace DuplicatePrefix.GeneralBorrowProtectedMutableStage
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowGeneratedStarShape (Star)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual protected mutable constructor retains the exact root-star graph;
this statement says nothing about root permissions while the child is held. -/
theorem slot_star (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (star : Star tree root node)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (covered : GeneralBorrowGraph.RootsCover tree) (parentTag tag : BorTag)
    (lookup : tree.tagMapping.get parentTag = some root) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (slot : GeneralBorrowFreshReborrowStages.Slot tree depth root) (offset len : UInt64) (nonzero : len ≠ 0)
    (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    ∃ next, Star (GeneralBorrowFreshMetadataChildMutableSlot.result tree parentTag tag offset len) root next := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,depth,children,covered,parentTag,tag,root,node,lookup,star.present,fresh,noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
    have raw := GeneralBorrowGeneratedStarShape.attached_star tree root node (GeneralBorrowFreshMetadataChildMutable.index input)
      (GeneralBorrowFreshChild.child tag root) star (GeneralBorrowFreshMetadataChildMutable.at_end input) rfl rfl
    have nodes : (GeneralBorrowFreshMetadataChildMutable.stage input).nodes =
        (GeneralBorrowFreshGraph.attached tree (GeneralBorrowFreshMetadataChildMutable.index input) root node (GeneralBorrowFreshChild.child tag root)).nodes := by
      simp only [GeneralBorrowFreshMetadataChildMutable.stage,GeneralBorrowFreshMetadataChildAttach.staged,input,GeneralBorrowFreshMetadataChildMutable.index]
    have staged := GeneralBorrowGeneratedStarShape.of_nodes _ (GeneralBorrowFreshMetadataChildMutable.stage input) root
      (GeneralBorrowFreshGraph.updatedParent node (GeneralBorrowFreshMetadataChildMutable.index input)) nodes raw
    exact GeneralBorrowGeneratedStarShape.shaped _ _ root _ (GeneralBorrowFreshMetadataChildMutable.shape input) staged
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,tag,root,node,lookup,star.present,fresh,index,available,bounded,vacant,slack,offset,len,nonzero,well,bounds⟩
    have raw := GeneralBorrowGeneratedReuseStarShape.attached_star tree root node index (GeneralBorrowFreshChild.child tag root) star vacant rfl rfl
    have nodes : (GeneralBorrowFreshMetadataChildMutableReuse.stage input).nodes =
        (GeneralBorrowFreshGraph.attached tree index root node (GeneralBorrowFreshChild.child tag root)).nodes := by
      simp only [GeneralBorrowFreshMetadataChildMutableReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,input,GeneralBorrowFreshMetadataChildMutableReuse.index]
    have staged := GeneralBorrowGeneratedStarShape.of_nodes _ (GeneralBorrowFreshMetadataChildMutableReuse.stage input) root
      (GeneralBorrowFreshGraph.updatedParent node index) nodes raw
    exact GeneralBorrowGeneratedStarShape.shaped _ _ root _ (GeneralBorrowFreshMetadataChildMutableReuse.shape input) staged

/-- Actual Read under the newly registered protector. -/
def read (tree : BorrowTree) (parentTag tag : BorTag) (offset len : UInt64) (global : GlobalState) (allocation : AllocId) :=
  tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read
    (GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.protectedTags .VisitChildrenOfAccessed

def child (tree : BorrowTree) (parentTag tag : BorTag) (offset len : UInt64) (global : GlobalState) (allocation : AllocId) :=
  (read tree parentTag tag offset len global allocation).tree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true

set_option autoImplicit false in
/-- The protected child contract, deliberately excluding active-protector root
ownership. Every field is formed from initial State by prepare below. -/
structure Data (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (tag : BorTag) (offset len : UInt64) (protections : ProtectedTags) where
  index : UniIndex
  node : TreeNode
  rootNode : TreeNode
  present : tree.nodeAt index = some node
  parent : node.parent = some root
  unexposed : node.isExposed = false
  rootPresent : tree.nodeAt root = some rootNode
  rootless : rootNode.parent = none
  lookup : tree.indexOfTag tag = some index
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates tree
  roots : tree.roots = #[root]
  fits : tree.nodes.data.size ≤ 4294967296
  well : tree.locations.WellFormed
  capacity : tree.locations.size = Size.ofBytes bytes
  bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat
  active : GeneralBorrowFreshActiveWithin.ActiveWithin tree index .Write offset (offset+len)
  owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections index .Write) offset (offset+len) tree.locations

/-- Fresh source registration and actual protected Read/reservation form the
protected child contract internally, for actual append and vacant-slot reuse. -/
theorem prepare (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (global : GlobalState) (empty : global.protectedTags = {}) (allocation : AllocId) :
    (read tree s.node.tag tag offset len global allocation).status = .Completed ∧
    (child tree s.node.tag tag offset len global allocation).outcome = .ok () ∧
    Nonempty (Data (child tree s.node.tag tag offset len global allocation).tree root capacity tag offset len
      (GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.protectedTags) := by
  let entry := GeneralBorrowPartitionEntryData.data tree root capacity s tag fresh
  let protections := (GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.protectedTags
  have heldEq : protections = ({} : ProtectedTags).insert tag .StrongProtector := by
    simp only [protections,GeneralBorrowProtectedMutableRelease.registration,GlobalState.addProtector,empty]
  have request : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat := by rw [s.capacity];exact bounds
  have owners : OwnedOn (GeneralBorrowRange.LocationOwned tree {} root .Write) offset (offset+len) tree.locations := by
    intro position valid positive lower upper;exact s.owned position valid
  have slotClean := s.clean _ (GeneralBorrowFreshMutableStages.slot_vacant tree entry.depth root entry.slot)
  have borrowed := GeneralBorrowFreshMutableStages.borrow tree {} s.node.tag tag root root s.node entry.depth entry.children
    s.star.present s.roots entry.covered (s.allocator.nodeTags root s.node s.star.present) fresh entry.protectorFresh entry.nodeFits
    entry.slot offset len nonzero s.well request owners slotClean
  rw [←heldEq] at borrowed
  have registeredOwners := GeneralBorrowFreshReadFrame.protector_owned_on tree {} tag .StrongProtector entry.protectorFresh root .Write offset (offset+len) owners
  rw [←heldEq] at registeredOwners
  have accessed := GeneralBorrowRangeLocal.access tree protections s.node.tag root root (Size.ofBytes offset) (Size.ofBytes len)
    .Read .Write .VisitChildrenOfAccessed (fun _ => rfl) entry.nodeFits entry.depth entry.children s.node s.star.present s.roots entry.covered
    (s.allocator.nodeTags root s.node s.star.present) s.well offset (offset+len) registeredOwners request (Nat.le_refl _) (Nat.le_refl _)
  let accessedTree := (read tree s.node.tag tag offset len global allocation).tree
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete s.node.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
  have nodes : accessedTree.nodes = tree.nodes := by simpa only [accessedTree,read] using congrArg BorrowTree.nodes frame
  have mapping : accessedTree.tagMapping = tree.tagMapping := by simpa only [accessedTree,read] using congrArg BorrowTree.tagMapping frame
  have rootsEq : accessedTree.roots = tree.roots := by simpa only [accessedTree,read] using congrArg BorrowTree.roots frame
  let nextDepth := GeneralBorrowFreshReadFrame.depth_on tree accessedTree nodes entry.depth
  have nextChildren : GeneralBorrowGraph.ChildNodes accessedTree := by rw [show accessedTree = {tree with locations := accessedTree.locations} from frame];exact entry.children
  have nextCovered : GeneralBorrowGraph.RootsCover accessedTree := by rw [show accessedTree = {tree with locations := accessedTree.locations} from frame];exact entry.covered
  have presentAfter : accessedTree.nodeAt root = some s.node := by change accessedTree.nodes.get root = some s.node;rw [nodes];exact s.star.present
  have taggedAfter : accessedTree.indexOfTag s.node.tag = some root := by change accessedTree.tagMapping.get s.node.tag = some root;rw [mapping];exact s.allocator.nodeTags root s.node s.star.present
  have freshAfter : GeneralBorrowTagMap.Fresh accessedTree.tagMapping tag := by rw [mapping];exact fresh
  have fitsAfter : accessedTree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact entry.nodeFits
  have boundsAfter : offset.toNat+len.toNat ≤ accessedTree.locations.size.bytes.toNat := by rw [show accessedTree.locations.size = tree.locations.size from accessed.2.2.2];exact request
  let slot := GeneralBorrowFreshMetadataChildMutableSlot.transport tree accessedTree entry.depth nextDepth nodes mapping rfl root entry.slot
  have indexEq := GeneralBorrowFreshMetadataChildMutableSlot.transport_index tree accessedTree entry.depth nextDepth nodes mapping rfl root entry.slot
  have metadata := GeneralBorrowFreshMetadataChildMutableSlot.build accessedTree nextDepth nextChildren nextCovered s.node.tag tag root s.node taggedAfter presentAfter
    freshAfter slot offset len nonzero accessed.2.2.1 fitsAfter boundsAfter
  have accessedStar := GeneralBorrowGeneratedStarShape.of_nodes tree accessedTree root s.node nodes s.star
  obtain ⟨rootNode,star⟩ := slot_star accessedTree root s.node accessedStar nextDepth nextChildren nextCovered s.node.tag tag taggedAfter freshAfter
    slot offset len nonzero accessed.2.2.1 boundsAfter
  obtain ⟨node,present,tagged,unexposed⟩ := metadata.node
  have initialIndex : GeneralBorrowFreshMutableStages.slot_index entry.slot = GeneralBorrowFreshMetadataChildMutableSlot.index entry.slot := by cases entry.slot <;> rfl
  have owned : OwnedOn (GeneralBorrowRange.LocationOwned (child tree s.node.tag tag offset len global allocation).tree protections
      (GeneralBorrowFreshMetadataChildMutableSlot.index slot) .Write) offset (offset+len) (child tree s.node.tag tag offset len global allocation).tree.locations := by
    rw [show GeneralBorrowFreshMetadataChildMutableSlot.index slot = GeneralBorrowFreshMetadataChildMutableSlot.index entry.slot from indexEq]
    rw [←initialIndex]
    exact borrowed.2.2.1
  have active : GeneralBorrowFreshActiveWithin.ActiveWithin (child tree s.node.tag tag offset len global allocation).tree
      (GeneralBorrowFreshMetadataChildMutableSlot.index slot) .Write offset (offset+len) := by
    rw [show GeneralBorrowFreshMetadataChildMutableSlot.index slot = GeneralBorrowFreshMetadataChildMutableSlot.index entry.slot from indexEq]
    rw [←initialIndex]
    exact borrowed.2.2.2
  have different : GeneralBorrowFreshMetadataChildMutableSlot.index slot ≠ root := by
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildMutableSlot.index entry.slot) = none := by rw [←initialIndex];exact GeneralBorrowFreshMutableStages.slot_vacant tree entry.depth root entry.slot
    intro same
    have equal : GeneralBorrowFreshMetadataChildMutableSlot.index entry.slot = root := indexEq.symm.trans same
    rw [equal,show tree.nodes.get root = some s.node from s.star.present] at vacant;cases vacant
  have parent := (star.leaves _ node present different).1
  refine ⟨borrowed.1,borrowed.2.1,⟨⟨GeneralBorrowFreshMetadataChildMutableSlot.index slot,node,rootNode,present,parent,unexposed,
    star.present,star.parentless,metadata.lookup,metadata.certificates,metadata.roots.trans (rootsEq.trans s.roots),metadata.nodeFits,
    metadata.well,?_,?_,active,owned⟩⟩⟩
  · exact metadata.capacity.trans (accessed.2.2.2.trans s.capacity)
  · rw [show (child tree s.node.tag tag offset len global allocation).tree.locations.size = accessedTree.locations.size from metadata.capacity]
    exact boundsAfter

end DuplicatePrefix.GeneralBorrowProtectedMutableStage
