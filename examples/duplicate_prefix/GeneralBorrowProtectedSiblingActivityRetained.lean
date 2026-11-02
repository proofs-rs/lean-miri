import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
import duplicate_prefix.GeneralBorrowProtectedSiblingActivityConstructor
import duplicate_prefix.GeneralBorrowProtectedSiblingActivityGc
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingActivityRetained
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

private theorem staged_node (tree : BorrowTree) (index parent query : UniIndex) (parentNode newNode node : TreeNode)
    (parentPresent : tree.nodeAt parent = some parentNode) (present : tree.nodeAt query = some node)
    (vacant : tree.nodes.get index = none) :
    ∃ next,(GeneralBorrowFreshGraph.attached tree index parent parentNode newNode).nodeAt query = some next ∧ next.tag = node.tag := by
  by_cases same : query = parent
  · subst query
    have equal : parentNode = node := Option.some.inj (parentPresent.symm.trans present)
    let updated : TreeNode := {parentNode with children := parentNode.children.push index}
    refine ⟨updated,?_,by dsimp only [updated];rw [←equal]⟩
    have found := GeneralBorrowFreshLocation.get_same (tree.nodes.insert index newNode) parent updated
    simpa only [GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt,GeneralBorrowFreshNode.attachedNodes,updated] using found
  · have different : query ≠ index := by intro equal;rw [←equal] at vacant;rw [show tree.nodes.get query = some node from present] at vacant;cases vacant
    let updated : TreeNode := {parentNode with children := parentNode.children.push index}
    have found : ((tree.nodes.insert index newNode).insert parent updated).get query = some node := by
      rw [GeneralBorrowFreshLocation.get_other (tree.nodes.insert index newNode) parent query updated same,GeneralBorrowFreshLocation.get_other tree.nodes index query newNode different]
      exact present
    exact ⟨node,by simpa only [GeneralBorrowFreshGraph.attached,BorrowTree.nodeAt,GeneralBorrowFreshNode.attachedNodes,updated] using found,rfl⟩

theorem append_node (input : GeneralBorrowFreshMetadataChildMutable.Input) (query : UniIndex) (node : TreeNode)
    (present : input.tree.nodeAt query = some node) :
    ∃ next,(GeneralBorrowFreshMetadataChildMutable.result input).nodeAt query = some next ∧ next.tag = node.tag := by
  have vacant : input.tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by simp [UniValMap.get,GeneralBorrowFreshMetadataChildMutable.at_end input]
  obtain ⟨staged,found,tagged⟩ := staged_node input.tree (GeneralBorrowFreshMetadataChildMutable.index input) input.parent query input.parentNode
    (GeneralBorrowFreshChild.child input.newTag input.parent) node input.parentPresent present vacant
  have atStage : (GeneralBorrowFreshMetadataChildMutable.stage input).nodeAt query = some staged := found
  obtain ⟨next,found,tag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields (GeneralBorrowFreshMetadataChildMutable.stage input) (GeneralBorrowFreshMetadataChildMutable.result input) (GeneralBorrowFreshMetadataChildMutable.shape input) query staged atStage
  exact ⟨next,found,tag.trans tagged⟩

theorem reuse_node (input : GeneralBorrowFreshMetadataChildMutableReuse.Input) (query : UniIndex) (node : TreeNode)
    (present : input.tree.nodeAt query = some node) :
    ∃ next,(GeneralBorrowFreshMetadataChildMutableReuse.result input).nodeAt query = some next ∧ next.tag = node.tag := by
  obtain ⟨staged,found,tagged⟩ := staged_node input.tree input.index input.parent query input.parentNode
    (GeneralBorrowFreshChild.child input.newTag input.parent) node input.parentPresent present input.vacant
  have atStage : (GeneralBorrowFreshMetadataChildMutableReuse.stage input).nodeAt query = some staged := found
  obtain ⟨next,found,tag,_,_,_⟩ := GeneralBorrowFreshMetadata.node_fields (GeneralBorrowFreshMetadataChildMutableReuse.stage input) (GeneralBorrowFreshMetadataChildMutableReuse.result input) (GeneralBorrowFreshMetadataChildMutableReuse.shape input) query staged atStage
  exact ⟨next,found,tag.trans tagged⟩

/-- Real fresh append and full collector retain the same live-tagged child
and strict interval. Collector error prefixes preserve these data as well. -/
theorem append_collect (input : GeneralBorrowFreshMetadataChildMutable.Input) (query : UniIndex) (node : TreeNode)
    (present : input.tree.nodeAt query = some node) (ownerKind : AccessKind) (lower upper : UInt64)
    (active : ActiveWithin input.tree query ownerKind lower upper) (live : Array BorTag) (held : live.contains node.tag = true) :
    ∃ next,((GeneralBorrowFreshMetadataChildMutable.result input).removeUnreachableTags live).tree.nodeAt query = some next ∧ next.tag = node.tag ∧
      ActiveWithin ((GeneralBorrowFreshMetadataChildMutable.result input).removeUnreachableTags live).tree query ownerKind lower upper := by
  obtain ⟨child,found,tagged⟩ := append_node input query node present
  have kept := GeneralBorrowProtectedSiblingActivityConstructor.append input query node present ownerKind lower upper active
  obtain ⟨next,found,tag,active⟩ := GeneralBorrowProtectedSiblingActivityGc.retained (GeneralBorrowFreshMetadataChildMutable.result input) live query child found (by rw [tagged];exact held) ownerKind lower upper kept
  exact ⟨next,found,tag.trans tagged,active⟩

/-- Reused vacant-slot constructors and the real full collector also keep
the same retained child and its original strict activity bounds. -/
theorem reuse_collect (input : GeneralBorrowFreshMetadataChildMutableReuse.Input) (query : UniIndex) (node : TreeNode)
    (present : input.tree.nodeAt query = some node) (ownerKind : AccessKind) (lower upper : UInt64)
    (active : ActiveWithin input.tree query ownerKind lower upper) (live : Array BorTag) (held : live.contains node.tag = true) :
    ∃ next,((GeneralBorrowFreshMetadataChildMutableReuse.result input).removeUnreachableTags live).tree.nodeAt query = some next ∧ next.tag = node.tag ∧
      ActiveWithin ((GeneralBorrowFreshMetadataChildMutableReuse.result input).removeUnreachableTags live).tree query ownerKind lower upper := by
  obtain ⟨child,found,tagged⟩ := reuse_node input query node present
  have kept := GeneralBorrowProtectedSiblingActivityConstructor.reuse input query node present ownerKind lower upper active
  obtain ⟨next,found,tag,active⟩ := GeneralBorrowProtectedSiblingActivityGc.retained (GeneralBorrowFreshMetadataChildMutableReuse.result input) live query child found (by rw [tagged];exact held) ownerKind lower upper kept
  exact ⟨next,found,tag.trans tagged,active⟩

/-- Any old child, including the current reborrow parent, retains its activity
through the real leading Read and append when the requested window lies inside
its existing activity interval. This complements the arbitrary-overlap foreign
sibling theorem; no successful Read/constructor premise is supplied. -/
theorem contained_read_append (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (roots : input.tree.roots = #[input.parent])
    (readable : GeneralRangeMapState.Every (GeneralBorrowProtectedReadRelease.Profile input.tree protections) input.tree.locations)
    (clean : GeneralBorrowGcVacantClean.VacantClean input.tree)
    (query : UniIndex) (node : TreeNode) (present : input.tree.nodeAt query = some node)
    (lower upper : UInt64) (requestLower : lower.toNat ≤ input.offset.toNat) (requestUpper : (input.offset+input.len).toNat ≤ upper.toNat)
    (active : ActiveWithin input.tree query .Write lower upper) :
    ∃ next,(GeneralBorrowProtectedReadableStage.child input protections).tree.nodeAt query = some next ∧ next.tag = node.tag ∧
      ActiveWithin (GeneralBorrowProtectedReadableStage.child input protections).tree query .Write lower upper := by
  have vacant : input.tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by simp [UniValMap.get,GeneralBorrowFreshMetadataChildMutable.at_end input]
  let prepared := GeneralBorrowProtectedReadableStage.prepare input protections roots readable (clean _ vacant)
  have afterRead := GeneralBorrowFreshActiveWithinAccess.normal input.tree input.parentTag (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read
    protections .VisitChildrenOfAccessed query lower upper input.well input.bounds requestLower requestUpper active
  have readFrame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read protections .VisitChildrenOfAccessed
  change (GeneralBorrowProtectedReadableStage.read input protections).tree = {input.tree with locations := (GeneralBorrowProtectedReadableStage.read input protections).tree.locations} at readFrame
  have beforePresent : prepared.next.tree.nodeAt query = some node := by rw [prepared.tree,readFrame];exact present
  obtain ⟨child,found,tagged⟩ := append_node prepared.next query node beforePresent
  have preparedActive : ActiveWithin prepared.next.tree query .Write lower upper := by rw [prepared.tree];exact afterRead
  have kept := GeneralBorrowProtectedSiblingActivityConstructor.append prepared.next query node beforePresent .Write lower upper preparedActive
  rw [prepared.result] at found kept
  exact ⟨child,found,tagged,kept⟩

/-- A real leading Read at the parent, real append and actual stack-protector
root collection retain the earlier child for real full GC. Every source premise
is raw initial data; neither constructor nor collector success is assumed. -/
theorem read_append_stack_collect (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (roots : input.tree.roots = #[input.parent])
    (readable : GeneralRangeMapState.Every (GeneralBorrowProtectedReadRelease.Profile input.tree protections) input.tree.locations)
    (clean : GeneralBorrowGcVacantClean.VacantClean input.tree)
    (query : UniIndex) (node : TreeNode) (present : input.tree.nodeAt query = some node) (parent : node.parent = some input.parent)
    (lower upper : UInt64) (active : ActiveWithin input.tree query .Write lower upper)
    (gcRoots : ProvenanceGC.Roots) (stack : ThreadStacks.ActualStack) (raw : GeneralBorrowGcFrameProvenanceStack.StackForm stack)
    (frameIndex : Nat) (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrow : FrameState) (id : AllocId)
    (framePresent : stack.frames[frameIndex]? = some frame) (borrowPresent : frame.extra.borrowTracker = some borrow)
    (stored : (id,node.tag) ∈ borrow.protectedTags) :
    ∃ collected,gcRoots.stack stack = .ok collected ∧ collected.allocations.contains id = true ∧
      ∃ next,((GeneralBorrowProtectedReadableStage.child input protections).tree.removeUnreachableTags collected.tags).tree.nodeAt query = some next ∧
        next.tag = node.tag ∧ ActiveWithin ((GeneralBorrowProtectedReadableStage.child input protections).tree.removeUnreachableTags collected.tags).tree query .Write lower upper := by
  have vacant : input.tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by simp [UniValMap.get,GeneralBorrowFreshMetadataChildMutable.at_end input]
  let prepared := GeneralBorrowProtectedReadableStage.prepare input protections roots readable (clean _ vacant)
  have readFrame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read protections .VisitChildrenOfAccessed
  change (GeneralBorrowProtectedReadableStage.read input protections).tree = {input.tree with locations := (GeneralBorrowProtectedReadableStage.read input protections).tree.locations} at readFrame
  have beforePresent : prepared.next.tree.nodeAt query = some node := by rw [prepared.tree,readFrame];exact present
  obtain ⟨child,found,tagged⟩ := append_node prepared.next query node beforePresent
  rw [prepared.result] at found
  have kept := GeneralBorrowProtectedSiblingActivityConstructor.read_append input protections roots readable clean query node present parent lower upper active
  obtain ⟨collected,actual,allocation,next,found,tag,active⟩ := GeneralBorrowProtectedSiblingActivityGc.stack_protector
    (GeneralBorrowProtectedReadableStage.child input protections).tree query child found .Write lower upper kept gcRoots stack raw frameIndex frame borrow id framePresent borrowPresent (by rw [tagged];exact stored)
  exact ⟨collected,actual,allocation,next,found,tag.trans tagged,active⟩
end DuplicatePrefix.GeneralBorrowProtectedSiblingActivityRetained
