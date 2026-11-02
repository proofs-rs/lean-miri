import duplicate_prefix.DuplicatePrefixVirtualWriteBothClosure
import duplicate_prefix.GeneralBorrowResidualVirtualWriteRuntime

namespace DuplicatePrefix.GeneralBorrowResidualVirtualWriteBothRuntime
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The two checked closures refer to the same deterministic real virtual
Write callback. Joining them adds physical runtime preservation to both full
query-pair authorization candidates; no future-operation certificate is input.
Initial Read authorization is not required: raw Write authorization supplies
the returned Read capability. This remains one callback, not a whole call. -/
theorem of_authorization (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (virtual : position ≠ 0)
    (support : UniIndex → Prop)
    (authorization : Authorization tree initial protections root position maximum .Write support)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree initial protections).topology)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections true
    result.status = .Completed ∧
      Authorization tree result.location protections root position maximum .Write support ∧
      Authorization tree result.location protections root position maximum .Read support ∧
      Snapshot tree result.location protections root position maximum .Write support ∧
      Snapshot tree result.location protections root position maximum .Read support ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      (∀ query, ¬support query → result.location.perms.get query = initial.perms.get query) ∧
      GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
      (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) := by
  obtain ⟨complete,writeAfter,readAfter,writeSnapshot,readSnapshot,afterCoherent,outside⟩ :=
    DuplicatePrefixVirtualWriteBothClosure.of_authorization tree initial protections root position maximum virtual
      support authorization depth forest coherent short
  obtain ⟨_,removed,legal,matching,_,_,afterProfile,afterPossible,vacant⟩ :=
    GeneralBorrowResidualVirtualWriteRuntime.of_authorization tree initial protections root position maximum virtual
      support authorization depth forest coherent short profile possible
  exact ⟨complete,writeAfter,readAfter,writeSnapshot,readSnapshot,afterCoherent,outside,afterProfile,afterPossible,vacant⟩

end DuplicatePrefix.GeneralBorrowResidualVirtualWriteBothRuntime
