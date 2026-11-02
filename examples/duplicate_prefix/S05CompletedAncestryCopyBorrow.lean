import duplicate_prefix.S05CompletedAncestryRangeRead
import duplicate_prefix.S05CompletedAncestryRangeWrite
import duplicate_prefix.GeneralBorrowRangeOutsideOwned
import duplicate_prefix.GeneralBorrowForestCopyBorrow

/-! Borrowing for the existing adjacent-copy operation. Source Read and
nonoverlapping destination Write consume initial buffer authority;
current destination authority is transported by physical-byte framing. -/
namespace DuplicatePrefix.S05CompletedAncestryCopyBorrow
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath OrdinaryBorrowAuthority
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality GeneralBorrowProjection
open GeneralRangeMapOrigins GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem completion_locations (tree : BorrowTree) (completion : Completion)
    (locations : DedupRangeMap LocationTree) (complete : Completes tree completion) :
    Completes {tree with locations := locations} completion := by
  refine ⟨complete.1,complete.2.1,complete.2.2.1,complete.2.2.2.1,complete.2.2.2.2.1,?_,complete.2.2.2.2.2.2⟩
  intro position root slot
  have original := complete.2.2.2.2.2.1 position root slot
  by_cases zero : position = 0
  · simpa only [zero,↓reduceIte] using original
  · simp only [zero,↓reduceIte] at original ⊢
    obtain ⟨earlier,originRoot,origin,rootNode,originNode,older,earlierSlot,rootHere,originHere,exposed,ordered,path,parent⟩ := original
    exact ⟨earlier,originRoot,origin,rootNode,originNode,older,earlierSlot,rootHere,originHere,exposed,ordered,
      GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := {tree with locations := locations}) (after := tree) rfl path,parent⟩

private theorem runtime_nodes (before after : BorrowTree) (nodes : after.nodes = before.nodes)
    (location : LocationTree) (protections : ProtectedTags)
    (runtime : LocationCoherent before location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile before location protections) :
    LocationCoherent after location protections ∧ GeneralBorrowLocationSifaConsistency.Profile after location protections := by
  refine ⟨?_,⟨?_,?_⟩⟩
  · simpa only [LocationCoherent,nodes] using runtime.1
  · intro index node present
    exact runtime.2.present index node (by simpa only [BorrowTree.nodeAt,nodes] using present)
  · intro index absent
    exact runtime.2.vacant index (by simpa only [nodes] using absent)

private theorem mutable_read (tree : BorrowTree) (completion : Completion) (location : LocationTree)
    (protections : ProtectedTags) (complete : Completes tree completion)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (fits : tree.nodes.data.size ≤ 4294967296)
    (position : Nat) (root source : UniIndex) (rootNode : TreeNode)
    (slot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePath : Path tree root source)
    (authority : ∀ index node, tree.nodes.get index = some node →
      (Below completion index source → LocalWrite
        ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
      (¬Below completion index source → ForeignWrite
        ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))) :
    ∀ index node, tree.nodes.get index = some node → Path tree root index →
      DuplicatePrefixScalarAuthorization.Compatible ((location.perms.get index).getD node.defaultLocationState) .Read
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) source.toNat index.toNat)
        (protections.contains node.tag) := by
  obtain ⟨actual,found,parentless⟩ := complete.2.2.2.1 position root slot
  have same : actual = rootNode := Option.some.inj (found.symm.trans rootPresent)
  subst actual
  obtain ⟨forest⟩ := formed.forest location protections
  obtain ⟨sourceNode,sourcePresent⟩ := sourcePath.present
  intro index node present path
  have physical := CompletedBorrowPhysicalSource.same_root_ancestor_iff complete rootPresent parentless present path sourcePath
  have related := GeneralBorrowProjectedDescPath.relation_local_iff tree location protections fits depth forest
    source index sourceNode node sourcePresent present
  by_cases localPath : Path tree index source
  · rw [related.mpr localPath]
    exact OrdinaryBorrowAuthorityBridge.local_scalar _ _ ((authority index node present).1 (physical.mpr localPath)) .Read
  · have foreignRelation : GeneralBorrowAnchor.relation (source_normal_projection tree location protections)
        source.toNat index.toNat = .ForeignAccess := by
      cases relation : GeneralBorrowAnchor.relation (source_normal_projection tree location protections) source.toNat index.toNat with
      | LocalAccess => exact False.elim (localPath (related.mp relation))
      | ForeignAccess => rfl
    rw [foreignRelation]
    have raw := (authority index node present).2 (fun below => localPath (physical.mp below))
    obtain ⟨next,delta,success,_⟩ := S05RawAuthorityStepPreservation.foreign_step _ _ .Read raw
    exact (DuplicatePrefixScalarAuthorization.compatible_iff _ .Read .ForeignAccess _ raw.1).mpr ⟨next,delta,success⟩

/-- The existing adjacent-copy borrow sequence consumes only initial buffer
rights. Destination rights after source Read follow from disjoint byte framing,
not from a future-state or successful-operation assumption. -/
theorem accesses (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (sourcePath : Path tree selected source)
    (offset sliceLen count : UInt64)
    (owned : OwnedOn (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      ∀ index node, tree.nodes.get index = some node →
        (Below completion index source → LocalWrite
          ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
        (¬Below completion index source → ForeignWrite
          ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)))
      offset (offset+sliceLen) tree.locations)
    (well : tree.locations.WellFormed)
    (runtime : Every (fun location => LocationCoherent tree location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree location protections) tree.locations)
    (bounds : offset.toNat+sliceLen.toNat ≤ tree.locations.size.bytes.toNat)
    (twice : count.toNat+count.toNat ≤ sliceLen.toNat) (short : tree.nodes.size < 65536) :
    let read := tree.performBorrowAccessRange (.concrete sourceNode.tag) (Size.ofBytes offset) (Size.ofBytes count)
      .Read protections .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete sourceNode.tag) (Size.ofBytes (offset+count)) (Size.ofBytes count)
      .Write protections .VisitChildrenOfAccessed
    read.status = .Completed ∧ write.status = .Completed ∧
      write.tree.locations.WellFormed ∧ write.tree.locations.size = tree.locations.size ∧
      Every (fun location => LocationCoherent write.tree location protections ∧
        GeneralBorrowLocationSifaConsistency.Profile write.tree location protections) write.tree.locations := by
  let read := tree.performBorrowAccessRange (.concrete sourceNode.tag) (Size.ofBytes offset) (Size.ofBytes count)
    .Read protections .VisitChildrenOfAccessed
  let write := read.tree.performBorrowAccessRange (.concrete sourceNode.tag) (Size.ofBytes (offset+count)) (Size.ofBytes count)
    .Write protections .VisitChildrenOfAccessed
  have ranges := GeneralBorrowForestCopyBorrow.arithmetic offset sliceLen count tree.locations.size.bytes bounds twice
  have fits : tree.nodes.data.size ≤ 4294967296 := by
    have size : tree.nodes.data.size = tree.nodes.size := rfl
    rw [size];omega
  have first := S05CompletedAncestryRangeRead.access tree completion protections complete formed depth order
    selectedPosition selected source source selectedNode sourceNode selectedSlot selectedPresent sourcePath sourcePresent sourcePath
    (Size.ofBytes offset) (Size.ofBytes count) offset (offset+sliceLen)
    (by
      intro position valid positive beforeUpper afterLower
      have authority := owned position valid positive beforeUpper afterLower
      refine ⟨authority.1,?_,?_⟩
      · exact mutable_read tree completion _ protections complete formed depth fits selectedPosition selected source
          selectedNode selectedSlot selectedPresent sourcePath authority.2
      · intro _ _ _ _ index node present _
        exact authority.2 index node present)
    well runtime ranges.1 (Nat.le_refl _) ranges.2.2.2.1 short .VisitChildrenOfAccessed
  have same := GeneralBorrowFreshReadFrame.frame tree (.concrete sourceNode.tag) (Size.ofBytes offset) (Size.ofBytes count)
    .Read protections .VisitChildrenOfAccessed
  change read.tree = {tree with locations := read.tree.locations} at same
  have nodes : read.tree.nodes = tree.nodes := by
    have equal := congrArg (fun current : BorrowTree => current.nodes) same
    exact equal
  have nextComplete : Completes read.tree completion := by
    rw [same];exact completion_locations tree completion _ complete
  have nextFormed : GeneralBorrowStructuralHistoryState.GraphState read.tree := by
    rw [same];exact GeneralBorrowStructuralHistoryState.graph_locations tree _ formed
  have nextDepth := GeneralBorrowFreshReadFrame.depth_on tree read.tree nodes depth
  have nextOrder : ParentTagOrder read.tree := by rw [same];exact order
  have nextPath : Path read.tree selected source :=
    GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := read.tree) (after := tree) nodes.symm sourcePath
  have destination := GeneralBorrowRangeOutsideOwned.owned
    (fun location => GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      ∀ index node, tree.nodes.get index = some node →
        (Below completion index source → LocalWrite
          ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
        (¬Below completion index source → ForeignWrite
          ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)))
    tree (.concrete sourceNode.tag) (Size.ofBytes offset) (Size.ofBytes count) .Read protections .VisitChildrenOfAccessed
    well ranges.1 (offset+count) ((offset+count)+count)
    (fun point afterStart _ => Or.inr afterStart)
    (by
      intro position valid positive beforeUpper afterLower
      exact owned position valid (by omega) (by omega) (by omega))
  have nextRuntime : Every (fun location => LocationCoherent read.tree location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile read.tree location protections) read.tree.locations := by
    intro position valid
    exact runtime_nodes tree read.tree nodes _ protections (first.runtime position valid)
  have second := S05CompletedAncestryRangeWrite.access read.tree completion protections nextComplete nextFormed nextDepth nextOrder
    selectedPosition selected source selectedNode sourceNode (by rw [same];exact selectedSlot)
    (by rw [same];exact selectedPresent) (by rw [same];exact sourcePresent) nextPath
    (Size.ofBytes (offset+count)) (Size.ofBytes count) (offset+count) ((offset+count)+count)
    (by simpa only [GeneralBorrowSnapshotReadRuntime.GlobalPossible,BorrowTree.nodeAt,nodes] using destination)
    first.well nextRuntime (by rw [first.capacity];exact ranges.2.1) (Nat.le_refl _) (Nat.le_refl _)
    (by rw [nodes];exact short) .VisitChildrenOfAccessed
  refine ⟨first.completed,second.completed,second.well,second.capacity.trans first.capacity,?_⟩
  have writeNodes : write.tree.nodes = read.tree.nodes := second.nodes
  intro position valid
  exact runtime_nodes read.tree write.tree writeNodes _ protections (second.runtime position valid)

end DuplicatePrefix.S05CompletedAncestryCopyBorrow

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05CompletedAncestryCopyBorrow." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved adjacent-copy borrowing dependency {dependency}"
