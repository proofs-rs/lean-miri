import duplicate_prefix.CurrentCallEmptyEntryOrphanRelease
import duplicate_prefix.CurrentCallEmptyEntryRepairedProtectorDrop
import duplicate_prefix.CurrentCallEmptyEntryRepairedRowFrame
import duplicate_prefix.GeneralBorrowConcreteRangeEntry
namespace DuplicatePrefix.CurrentCallEmptyEntryOrphanOriginalWrite
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall GeneralRangeMapOrigins GeneralRangeMapState
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder GeneralBorrowExposureCardinality GeneralBorrowProjection
open CurrentCallEmptyEntryBool S05CompletedAncestryReadMutable
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000

private theorem parent_path (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (position : Nat) (root child parent : UniIndex) (node : TreeNode)
    (rootAt : tree.roots[position]?=some root) (present : tree.nodeAt child=some node)
    (edge : node.parent=some parent) (path : Path tree root child) : Path tree root parent := by
  cases path with
  | refl actual atNode =>
    obtain ⟨rootNode,atRoot,parentless⟩ := formed.rootNodes root
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootAt))
    have eq : rootNode=node := Option.some.inj (atRoot.symm.trans present)
    rw [eq,edge] at parentless
    contradiction
  | step earlier actual atNode actualEdge =>
    have eq : actual=node := Option.some.inj (atNode.symm.trans present)
    rw [eq,edge] at actualEdge
    cases Option.some.inj actualEdge
    exact earlier

private theorem callback (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree) (order : ParentTagOrder tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (root : UniIndex) (position : Nat) (maximum : Option BorTag)
    (support : UniIndex → Prop)
    (auth : DuplicatePrefixResidualWriteRepaired.Authorization tree initial protections root position maximum .Write support)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size<65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections (position != 0)
    result.status=.Completed ∧ LocationCoherent tree result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      ∀ query,¬support query → result.location.perms.get query=initial.perms.get query := by
  obtain ⟨forest⟩ := formed.forest initial protections
  have graph := GeneralBorrowExposedScopedReciprocal.of_forest tree initial protections forest depth
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree initial protections forest
  let area : GeneralBorrowWildcardControlStack.Support tree root := ⟨support,auth.rooted,auth.present,auth.children⟩
  have plans : Nonempty (DuplicatePrefixResidualWriteWitnessPlan.Plan tree initial protections root position maximum) := by
    by_cases zero : position=0
    · obtain ⟨witness,node,included,present,eligible⟩ := auth.witness zero
      have path := GeneralBorrowWildcardControlWitness.path_of_covers tree depth root witness node present (auth.covers witness included)
      subst position
      exact ⟨DuplicatePrefixResidualVisibleWritePlan.ordered tree initial protections root maximum depth graph short witness node present
        (GeneralBorrowPrimaryWitnessVisibility.of_order tree order initial protections maximum .Write witness node present eligible) eligible path⟩
    · exact ⟨DuplicatePrefixResidualWriteWitnessPlan.virtual tree initial protections root position maximum zero⟩
  obtain ⟨plan⟩ := plans
  obtain ⟨done,removed,_,_,cache,outside,sifa,gp,_⟩ := DuplicatePrefixResidualWriteRepaired.access tree initial protections root position maximum weights
    (GeneralBorrowWildcardForestWeights.bounded tree initial protections forest root) area plan auth depth forest coherent short profile possible
  exact ⟨done,cache,sifa,gp,outside⟩

/-- Original concrete-parent Write after the whole root frame's protector drop. -/
theorem range (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (tag qTag : BorTag) (provenance : Provenance) (offset : UInt64)
    (h : BoolHoldings tree global tag qTag provenance offset)
    (beforeRuntime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree (global.endCall frame)) (order : ParentTagOrder tree)
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame tree frame)
    (physical : h.node.parent=some h.parent)
    (factory : OrphanWriteFactory tree h.completion global.protectedTags h.child qTag)
    (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat) (short : tree.nodes.size<65536)
    (normal : OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree row (global.endCall frame).protectedTags h.parent)) offset (offset+1) tree.locations)
    (childOwned : OwnedOn (Authority tree h.completion global.protectedTags h.child) offset (offset+1) tree.locations) :
    (tree.performBorrowAccessRange (.concrete h.parentNode.tag) (Size.ofBytes offset) (Size.ofBytes 1) .Write
      (global.endCall frame).protectedTags .VisitChildrenOfAccessed).status=.Completed := by
  obtain ⟨depth⟩ := runtime.formed.depth
  have parentPath : Path tree factory.selected h.parent := parent_path tree runtime.formed.toGraphState
    factory.selectedPosition factory.selected h.child h.parent h.node factory.selectedSlot h.present physical factory.selectedPath
  have mapped := runtime.formed.allocator.nodeTags h.parent h.parentNode h.parentAt
  let P := fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree row (global.endCall frame).protectedTags h.parent) ∧
    Authority tree h.completion global.protectedTags h.child row ∧ GeneralBorrowLocationSifaConsistency.Profile tree row global.protectedTags
  let R := fun row => LocationCoherent tree row (global.endCall frame).protectedTags ∧
    GeneralBorrowLocationSifaConsistency.Profile tree row (global.endCall frame).protectedTags ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree row
  have owned : OwnedOn P offset (offset+1) tree.locations := by
    intro position valid positive start stop
    exact ⟨normal position valid positive start stop,childOwned position valid positive start stop,beforeRuntime.formed.profile position valid⟩
  have contract := GeneralBorrowConcreteRangeEntry.access tree (global.endCall frame).protectedTags h.parentNode.tag h.parent mapped
    (Size.ofBytes offset) (Size.ofBytes 1) .Write .VisitChildrenOfAccessed P (fun _=>True) R (fun _ _=>True)
    (fun _ _=>trivial) (fun _=>trivial) (by
      intro initial input representation range
      obtain ⟨parentNormal⟩ := input.1
      have scalar := CurrentCallEmptyEntryRootLoop.write tree initial (global.endCall frame).protectedTags runtime.formed.toGraphState factory.distinct
        factory.selectedPosition factory.selected h.parent factory.selectedNode h.parentNode factory.selectedSlot factory.selectedAt h.parentAt parentPath
        parentNormal representation.1 representation.2.1 representation.2.2 (by
          intro position root rootAt different current cache sifa gp currentFrame
          obtain ⟨queries⟩ := factory.callbacks initial input.2.1 position root rootAt different
            (by intro index node present path;exact input.2.2.present index node present)
          have dropped := CurrentCallEmptyEntryRepairedProtectorDrop.authorization tree initial global.protectedTags (global.endCall frame).protectedTags
            (GeneralBorrowRelease.end_call_weakens global frame) (S04ReturnReleaseParent.exposed_frame tree global frame hiddenFrame)
            root position (some factory.selectedNode.tag) .Write queries.support queries.authorization
          have framed := CurrentCallEmptyEntryRepairedRowFrame.authorization tree initial current (global.endCall frame).protectedTags depth
            root position (some factory.selectedNode.tag) .Write queries.support dropped currentFrame
          obtain ⟨done,afterCache,afterSifa,afterPossible,outside⟩ := callback tree current (global.endCall frame).protectedTags runtime.formed.toGraphState order depth
            root position (some factory.selectedNode.tag) queries.support framed cache short sifa gp
          exact ⟨done,afterCache,afterSifa,afterPossible,fun query notPath => outside query (fun included => notPath (queries.path query included))⟩)
        .VisitChildrenOfAccessed range
      exact ⟨scalar.1,trivial,scalar.2,trivial⟩)
    offset (offset+1) owned runtime.formed.well (by intro position valid;exact ⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid⟩)
    bounds (Nat.le_refl _) (Nat.le_refl _)
  exact contract.completed

/-- Post-release metadata form: activity and Write-only holdings are not required. -/
theorem range_metadata (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (completion : Completion) (child parent : UniIndex) (childNode parentNode : TreeNode) (qTag : BorTag) (offset : UInt64)
    (childAt : tree.nodeAt child=some childNode) (parentAt : tree.nodeAt parent=some parentNode)
    (physical : childNode.parent=some parent)
    (beforeRuntime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree (global.endCall frame)) (order : ParentTagOrder tree)
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame tree frame)
    (factory : OrphanWriteFactory tree completion global.protectedTags child qTag)
    (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat) (short : tree.nodes.size<65536)
    (normal : OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree row (global.endCall frame).protectedTags parent)) offset (offset+1) tree.locations)
    (childOwned : OwnedOn (Authority tree completion global.protectedTags child) offset (offset+1) tree.locations) :
    (tree.performBorrowAccessRange (.concrete parentNode.tag) (Size.ofBytes offset) (Size.ofBytes 1) .Write
      (global.endCall frame).protectedTags .VisitChildrenOfAccessed).status=.Completed := by
  obtain ⟨depth⟩ := runtime.formed.depth
  have parentPath : Path tree factory.selected parent := parent_path tree runtime.formed.toGraphState
    factory.selectedPosition factory.selected child parent childNode factory.selectedSlot childAt physical factory.selectedPath
  have mapped := runtime.formed.allocator.nodeTags parent parentNode parentAt
  let P := fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree row (global.endCall frame).protectedTags parent) ∧
    Authority tree completion global.protectedTags child row ∧ GeneralBorrowLocationSifaConsistency.Profile tree row global.protectedTags
  let R := fun row => LocationCoherent tree row (global.endCall frame).protectedTags ∧
    GeneralBorrowLocationSifaConsistency.Profile tree row (global.endCall frame).protectedTags ∧ GeneralBorrowSnapshotReadRuntime.GlobalPossible tree row
  have owned : OwnedOn P offset (offset+1) tree.locations := by
    intro position valid positive start stop
    exact ⟨normal position valid positive start stop,childOwned position valid positive start stop,beforeRuntime.formed.profile position valid⟩
  have contract := GeneralBorrowConcreteRangeEntry.access tree (global.endCall frame).protectedTags parentNode.tag parent mapped
    (Size.ofBytes offset) (Size.ofBytes 1) .Write .VisitChildrenOfAccessed P (fun _=>True) R (fun _ _=>True)
    (fun _ _=>trivial) (fun _=>trivial) (by
      intro initial input representation range
      obtain ⟨parentNormal⟩ := input.1
      have scalar := CurrentCallEmptyEntryRootLoop.write tree initial (global.endCall frame).protectedTags runtime.formed.toGraphState factory.distinct
        factory.selectedPosition factory.selected parent factory.selectedNode parentNode factory.selectedSlot factory.selectedAt parentAt parentPath
        parentNormal representation.1 representation.2.1 representation.2.2 (by
          intro position root rootAt different current cache sifa gp currentFrame
          obtain ⟨queries⟩ := factory.callbacks initial input.2.1 position root rootAt different
            (by intro index node present path;exact input.2.2.present index node present)
          have dropped := CurrentCallEmptyEntryRepairedProtectorDrop.authorization tree initial global.protectedTags (global.endCall frame).protectedTags
            (GeneralBorrowRelease.end_call_weakens global frame) (S04ReturnReleaseParent.exposed_frame tree global frame hiddenFrame)
            root position (some factory.selectedNode.tag) .Write queries.support queries.authorization
          have framed := CurrentCallEmptyEntryRepairedRowFrame.authorization tree initial current (global.endCall frame).protectedTags depth
            root position (some factory.selectedNode.tag) .Write queries.support dropped currentFrame
          obtain ⟨done,afterCache,afterSifa,afterPossible,outside⟩ := callback tree current (global.endCall frame).protectedTags runtime.formed.toGraphState order depth
            root position (some factory.selectedNode.tag) queries.support framed cache short sifa gp
          exact ⟨done,afterCache,afterSifa,afterPossible,fun query notPath => outside query (fun included => notPath (queries.path query included))⟩)
        .VisitChildrenOfAccessed range
      exact ⟨scalar.1,trivial,scalar.2,trivial⟩)
    offset (offset+1) owned runtime.formed.well (by intro position valid;exact ⟨runtime.coherent position valid,runtime.formed.profile position valid,runtime.possible position valid⟩)
    bounds (Nat.le_refl _) (Nat.le_refl _)
  exact contract.completed

end
end DuplicatePrefix.CurrentCallEmptyEntryOrphanOriginalWrite

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryOrphanOriginalWrite" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved orphan original Write dependency {dependency}"
