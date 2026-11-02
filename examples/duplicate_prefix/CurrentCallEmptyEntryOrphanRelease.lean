import duplicate_prefix.CurrentCallEmptyEntryBool
import duplicate_prefix.CurrentCallEmptyEntryBoolRelease
import duplicate_prefix.GeneralBorrowParentRestoreNormal
namespace DuplicatePrefix.CurrentCallEmptyEntryOrphanRelease
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall GeneralRangeMapOrigins GeneralBorrowExposedNonleafPrimaryPath
open GeneralBorrowWildcardParentTagOrder GeneralBorrowFreshActiveWithin GeneralBorrowExposureCardinality
open CurrentCallEmptyEntryBool
open S05CompletedAncestryReadMutable (Authority)
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Actual same-held-set Bool release on the finite orphan geometry. -/
theorem release (tree : BorrowTree) (global : GlobalState) (tag qTag : BorTag) (provenance : Provenance) (offset : UInt64)
    (holdings : BoolHoldings tree global tag qTag provenance offset)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (order : ParentTagOrder tree)
    (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat) (short : tree.nodes.size<65536)
    (factory : OrphanWriteFactory tree holdings.completion global.protectedTags holdings.child qTag) :
    let result := tree.releaseProtector tag global.protectedTags
    result.status=.Released ∧ result.tree={tree with locations:=result.tree.locations} ∧
      DuplicatePrefixBorrowContract.RuntimeFacts result.tree global ∧ result.tree.locations.size=tree.locations.size ∧
      OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal result.tree row global.protectedTags holdings.child) ∧
        Authority result.tree holdings.completion global.protectedTags holdings.child row) offset (offset+1) result.tree.locations := by
  have positive : offset.toNat<(offset+1).toNat := by
    have fits : offset.toNat+1<2^64 := Nat.lt_of_le_of_lt bounds tree.locations.size.bytes.toNat_lt
    rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt fits];omega
  have write : ∀ location,Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags holdings.child) →
      Authority tree holdings.completion global.protectedTags holdings.child location →
      LocationCoherent tree location global.protectedTags →
      GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags →
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location → ∀ range,
      let result := source_tree_access_at tree location (some holdings.child) .Write global.protectedTags .SkipChildrenOfAccessed range
      source_access_status result=none ∧ LocationCoherent tree (source_access_location result) global.protectedTags ∧
        GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) global.protectedTags ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree (source_access_location result) global.protectedTags holdings.child) ∧
        Authority tree holdings.completion global.protectedTags holdings.child (source_access_location result) := by
    intro initial normal authority coherent profile possible range
    obtain ⟨normal⟩ := normal
    apply CurrentCallEmptyEntryNormalWrite.write_authority tree holdings.completion initial global.protectedTags runtime.formed.toGraphState
      factory.distinct factory.selectedPosition factory.selected holdings.child factory.selectedNode holdings.node factory.selectedSlot
      factory.selectedAt holdings.present factory.selectedPath normal authority factory.selectedClassification coherent profile possible
    intro position root rootAt different current currentAuthority cache sifa gp currentFrame
    obtain ⟨queries⟩ := factory.callbacks current currentAuthority position root rootAt different
      (by intro index node present path;exact sifa.present index node present)
    obtain ⟨depth⟩ := runtime.formed.depth
    obtain ⟨done,afterCache,afterSifa,afterPossible,outside,rights⟩ := CurrentCallEmptyEntryWriteRetention.root tree current global.protectedTags
      runtime.formed.toGraphState order depth root position (some factory.selectedNode.tag) queries.support queries.authorization cache short sifa gp
      holdings.completion holdings.child queries.classification currentAuthority
    exact ⟨done,afterCache,afterSifa,afterPossible,(fun query notPath => outside query (fun included => notPath (queries.path query included))),rights⟩
  have result := CurrentCallEmptyEntryBoolRelease.release tree global holdings.completion runtime holdings.child holdings.node holdings.present
    holdings.hidden offset 1 positive holdings.active holdings.owned holdings.writeOnly write
  simpa only [holdings.nodeTag] using result

/-- Reanchor the real physical parent only after all root protectors have been released. -/
theorem restore_parent (tree : BorrowTree) (global : GlobalState) (tag qTag : BorTag) (provenance : Provenance) (offset : UInt64)
    (holdings : BoolHoldings tree global tag qTag provenance offset)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (order : ParentTagOrder tree)
    (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat) (short : tree.nodes.size<65536)
    (factory : OrphanWriteFactory tree holdings.completion global.protectedTags holdings.child qTag)
    (frame : FrameState) (allocation : AllocId) (member : (allocation,holdings.node.tag)∈frame.protectedTags.toList)
    (physical : holdings.node.parent=some holdings.parent) :
    let after := (tree.releaseProtector tag global.protectedTags).tree
    after.nodeAt holdings.parent=some holdings.parentNode ∧
      (match provenance with | .concrete _ oldTag => oldTag=holdings.parentNode.tag | .wildcard => holdings.parentNode.isExposed=true) ∧
      OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal after row (global.endCall frame).protectedTags holdings.parent) ∧
        Authority after holdings.completion (global.endCall frame).protectedTags holdings.parent row) offset (offset+1) after.locations ∧
      (S04ReturnReleaseParent.HiddenFrame after frame → DuplicatePrefixBorrowContract.RuntimeFacts after (global.endCall frame)) := by
  obtain ⟨_,shape,afterRuntime,_,afterOwned⟩ := release tree global tag qTag provenance offset holdings runtime order bounds short factory
  let after := (tree.releaseProtector tag global.protectedTags).tree
  have nodes : after.nodes=tree.nodes := by
    have framed := congrArg BorrowTree.nodes shape
    exact framed
  have childAt : after.nodeAt holdings.child=some holdings.node := by
    change after.nodes.get holdings.child=_;rw [nodes];exact holdings.present
  have parentAt : after.nodeAt holdings.parent=some holdings.parentNode := by
    change after.nodes.get holdings.parent=_;rw [nodes];exact holdings.parentAt
  have childOwned : OwnedOn (Authority after holdings.completion global.protectedTags holdings.child) offset (offset+1) after.locations := by
    intro position valid positive start stop
    exact (afterOwned position valid positive start stop).2
  have parentOwned := S05CompletedChildReanchor.owned_end_call after holdings.completion global frame allocation holdings.child holdings.parent
    holdings.node offset (offset+1) holdings.edge childAt member childOwned
  refine ⟨parentAt,(by cases provenance <;> exact holdings.parentProvenance),?_,fun hiddenFrame => S05CompletedChildReanchor.runtime_end_call after global frame afterRuntime hiddenFrame⟩
  intro position valid positive start stop
  obtain ⟨⟨normal⟩,_⟩ := afterOwned position valid positive start stop
  exact ⟨GeneralBorrowParentRestoreNormal.end_call after _ global frame allocation holdings.child holdings.parent holdings.node
    afterRuntime.formed.toGraphState childAt physical member normal,parentOwned position valid positive start stop⟩

end
end DuplicatePrefix.CurrentCallEmptyEntryOrphanRelease
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryOrphanRelease" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved orphan release dependency {dependency}"
