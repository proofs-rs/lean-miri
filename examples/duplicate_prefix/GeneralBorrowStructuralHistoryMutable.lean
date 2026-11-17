import duplicate_prefix.GeneralBorrowStructuralHistorySeed
import duplicate_prefix.GeneralBorrowFreshMutableSlotResources
import duplicate_prefix.GeneralBorrowFreshProtectedSlotOther
import duplicate_prefix.GeneralBorrowCanonicalParentDepth
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryMutable
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState GeneralBorrowExposure GeneralBorrowGraph GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
noncomputable section

def depth (tree : BorrowTree) (initial : State tree) : ParentDepth tree.nodes :=
  GeneralBorrowCanonicalParentDepth.normalize tree.nodes (Classical.choice initial.depth)

def slot (tree : BorrowTree) (initial : State tree) (parent : UniIndex) (node : TreeNode)
    (present : tree.nodeAt parent=some node) (room : tree.nodes.size+1 ≤ 4294967295) : Slot tree (depth tree initial) parent := by
  let old := Classical.choice initial.depth
  have aligned := GeneralBorrowFreshStagePool.empty_aligned tree initial.allocator.accounting
  have fits : tree.tagMapping.deassigned.back?=none → tree.tagMapping.mapping.size≤4294967295 := by
    intro empty
    rw [aligned empty]
    change tree.nodes.data.size+1 ≤ _ at room
    omega
  exact GeneralBorrowCanonicalParentDepth.slot tree old parent node present initial.allocator.pool aligned fits

private theorem parent_append (input : GeneralBorrowFreshMetadataChildMutable.Input) :
    ∃ node,(GeneralBorrowFreshMetadataChildMutable.result input).nodeAt input.parent=some node ∧ node.parent=input.parentNode.parent := by
  have present := GeneralBorrowFreshGraph.parent_lookup input.tree (GeneralBorrowFreshMetadataChildMutable.index input)
    input.parent input.parentNode (GeneralBorrowFreshChild.child input.newTag input.parent)
    (GeneralBorrowFreshMetadataChildMutable.at_end input) input.parentPresent
  have stage : (GeneralBorrowFreshMetadataChildMutable.stage input).nodeAt input.parent=
      some (GeneralBorrowFreshGraph.updatedParent input.parentNode (GeneralBorrowFreshMetadataChildMutable.index input)) := by
    simpa only [GeneralBorrowFreshMetadataChildMutable.stage,GeneralBorrowFreshMetadataChildAttach.staged,BorrowTree.nodeAt] using present
  obtain ⟨node,found,_,parents,_,_⟩ := GeneralBorrowFreshMetadata.node_fields _ _
    (GeneralBorrowFreshMetadataChildMutable.shape input) _ _ stage
  exact ⟨node,found,parents⟩

private theorem parent_reuse (input : GeneralBorrowFreshMetadataChildMutableReuse.Input) :
    ∃ node,(GeneralBorrowFreshMetadataChildMutableReuse.result input).nodeAt input.parent=some node ∧ node.parent=input.parentNode.parent := by
  have present := GeneralBorrowFreshMetadataChildReuseGraph.parent_lookup input.tree input.index
    input.parent input.parentNode (GeneralBorrowFreshChild.child input.newTag input.parent) input.vacant input.parentPresent
  have stage : (GeneralBorrowFreshMetadataChildMutableReuse.stage input).nodeAt input.parent=
      some (GeneralBorrowFreshGraph.updatedParent input.parentNode input.index) := by
    simpa only [GeneralBorrowFreshMetadataChildMutableReuse.stage,GeneralBorrowFreshMetadataChildMutableReuse.index,GeneralBorrowFreshMetadataChildAttach.staged,BorrowTree.nodeAt] using present
  obtain ⟨node,found,_,parents,_,_⟩ := GeneralBorrowFreshMetadata.node_fields _ _
    (GeneralBorrowFreshMetadataChildMutableReuse.shape input) _ _ stage
  exact ⟨node,found,parents⟩

/-- Every original root retains an actual parentless node through concrete
protected reservation, including reusing a genuinely vacant sparse slot. -/
theorem root_nodes (tree : BorrowTree) (rank : ParentDepth tree.nodes) (children : ChildNodes tree) (covered : RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.indexOfTag parentTag=some parent) (parentPresent : tree.nodeAt parent=some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (selected : Slot tree rank parent)
    (offset len : UInt64) (nonzero : len≠0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (roots : ∀root∈tree.roots.toList,∃node,tree.nodes.get root=some node ∧ node.parent=none) :
    ∀root∈tree.roots.toList,∃node,(GeneralBorrowFreshMetadataChildMutableSlot.result tree parentTag newTag offset len).nodes.get root=some node ∧ node.parent=none := by
  intro root member
  obtain ⟨old,present,parentless⟩ := roots root member
  by_cases same : root=parent
  · subst root
    have equal : old=parentNode := Option.some.inj (present.symm.trans parentPresent)
    subst old
    cases selected with
    | append noFree aligned fits =>
      let input : GeneralBorrowFreshMetadataChildMutable.Input :=
        ⟨tree,rank,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
      obtain ⟨node,found,parents⟩ := parent_append input
      exact ⟨node,found,parents.trans parentless⟩
    | reuse child available bounded vacant slack =>
      let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
        ⟨tree,rank,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,child,available,bounded,vacant,slack,offset,len,nonzero,well,bounds⟩
      obtain ⟨node,found,parents⟩ := parent_reuse input
      exact ⟨node,found,parents.trans parentless⟩
  · obtain ⟨node,found,_,parents,_,_,_⟩ := GeneralBorrowFreshProtectedSlotOther.of_slot tree rank children covered parentTag newTag parent parentNode
      parentTagPresent parentPresent fresh selected offset len nonzero well bounds root old present same
    exact ⟨node,found,parents.trans parentless⟩

/-- Actual protected Default reservation at an arbitrary raw present parent.
Slot choice and bounded reuse ranks are formed internally from intrinsic State;
no operation outcome or poststate certificate is supplied. -/
theorem construct (tree : BorrowTree) (initial : State tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.indexOfTag parentTag=some parent) (parentPresent : tree.nodeAt parent=some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1≤4294967295)
    (offset len : UInt64) (nonzero : len≠0) (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat) :
    let operation := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    operation.outcome=.ok () ∧ State operation.tree ∧ operation.tree.locations.size=tree.locations.size ∧
      operation.tree.nodes.size≤tree.nodes.size+1 := by
  dsimp only
  let rank := depth tree initial
  let selected := slot tree initial parent parentNode parentPresent room
  let after := GeneralBorrowFreshMetadataChildMutableSlot.result tree parentTag newTag offset len
  have metadata := GeneralBorrowFreshMetadataChildMutableSlot.build tree rank initial.children initial.covered parentTag newTag parent parentNode
    parentTagPresent parentPresent fresh selected offset len nonzero initial.well initial.fits bounds
  have resources := GeneralBorrowFreshMutableSlotResources.preserves tree rank initial.children initial.covered parentTag newTag parent parentNode
    parentTagPresent parentPresent fresh selected offset len nonzero initial.well bounds initial.allocator
  have completed : (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).outcome=.ok () := by
    cases selected with
    | append noFree aligned fits =>
      exact (GeneralBorrowFreshMetadataChildMutable.append
        ⟨tree,rank,initial.children,initial.covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,noFree,aligned,fits,offset,len,nonzero,initial.well,bounds⟩).success
    | reuse child available bounded vacant slack =>
      exact (GeneralBorrowFreshMetadataChildMutableReuse.reuse
        ⟨tree,rank,initial.children,initial.covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,child,available,bounded,vacant,slack,offset,len,nonzero,initial.well,bounds⟩).success
  refine ⟨completed,⟨⟨?_,⟨metadata.certificates.depth⟩,metadata.certificates.children,metadata.certificates.covered,?_,resources.1,metadata.nodeFits⟩,resources.2.1⟩,resources.2.2.1,resources.2.2.2⟩
  · intro location protections
    obtain ⟨forest⟩ := initial.forest location protections
    rcases metadata.extension location location protections with appended | reused
    · exact ⟨GeneralBorrowFreshTopology.extended_forest _ _ parent.toNat appended forest⟩
    · exact ⟨GeneralBorrowFreshReuseTopology.extended_forest _ _ _ parent.toNat reused forest⟩
  · intro root member
    change root ∈ (GeneralBorrowFreshMetadataChildMutableSlot.result tree parentTag newTag offset len).roots.toList at member
    rw [metadata.roots] at member
    exact root_nodes tree rank initial.children initial.covered parentTag newTag parent parentNode parentTagPresent parentPresent fresh selected
      offset len nonzero initial.well bounds initial.rootNodes root member
end
end DuplicatePrefix.GeneralBorrowStructuralHistoryMutable
