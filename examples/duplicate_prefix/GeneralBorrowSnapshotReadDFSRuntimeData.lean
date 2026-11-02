import duplicate_prefix.GeneralBorrowSnapshotReadRuntime
namespace DuplicatePrefix.GeneralBorrowSnapshotReadDFSRuntimeData
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowExposedNonleafState (ReadFrame updated)
open GeneralBorrowSnapshotReadState (wildcard)
open GeneralBorrowSnapshotReadRuntime (GlobalPossible)
set_option autoImplicit false
set_option maxRecDepth 65536
theorem post_optional (enabled : Bool) (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (maximum : Option BorTag) (support : UniIndex → Prop)
    (snapshot : Snapshot tree location protections root rootPosition maximum .Read support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (runtime : enabled = true → GeneralBorrowLocationSifaConsistency.Profile tree location protections ∧ GlobalPossible tree location)
    (index : UniIndex) (node : TreeNode) (included : support index) (present : tree.nodes.get index = some node)
    (recurse : DuplicatePrefixCallbackVisitAuthorization.entrySkip (effective location index node) .Read
      (relation location root index node maximum .Read rootPosition) = false) :
    ∃ after,
      ((relation location root index node maximum .Read rootPosition = some .EitherAccess ∧ after = materialized location index node) ∨
       ∃ exact recorded next delta,
         relation location root index node maximum .Read rootPosition = some (wildcard exact) ∧
         (effective location index node).recordNewAccess .Read exact = .Recorded recorded ∧
         recorded.performAccess .Read exact (protections.contains node.tag) = .Success next delta ∧
         after = updated tree location index node protections recorded next delta) ∧
      Snapshot tree after protections root rootPosition maximum .Read support ∧
      ReadFrame location after ∧ GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
      (∀ query, query ≠ index → after.perms.get query = location.perms.get query) ∧
      GeneralBorrowWildcardPrimaryReadWitness.PointwiseReadFrame tree protections location after ∧
      (enabled = true → GeneralBorrowLocationSifaConsistency.Profile tree after protections ∧ GlobalPossible tree after) := by
  cases enabled with
  | false =>
    obtain ⟨after,action,snapshot,frame,coherent,other,pointwise⟩ :=
      GeneralBorrowSnapshotReadSupport.post_with_support tree location protections root rootPosition maximum support
        snapshot depth coherent index node included present recurse
    exact ⟨after,action,snapshot,frame,coherent,other,pointwise,by simp⟩
  | true =>
    obtain ⟨profile,possible⟩ := runtime rfl
    obtain ⟨after,action,snapshot,frame,coherent,other,pointwise,profile,vacant,possible⟩ :=
      GeneralBorrowSnapshotReadRuntime.post_with_runtime tree location protections root rootPosition maximum support
        snapshot depth coherent profile possible index node included present recurse
    exact ⟨after,action,snapshot,frame,coherent,other,pointwise,fun _ => ⟨profile,possible⟩⟩
end DuplicatePrefix.GeneralBorrowSnapshotReadDFSRuntimeData
