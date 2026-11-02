import duplicate_prefix.GeneralBorrowSnapshotReadTransport
import duplicate_prefix.GeneralBorrowSnapshotVirtualReadAccess

namespace DuplicatePrefix.GeneralBorrowSnapshotReadOtherRoot
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection DuplicatePrefixCallbackAuthorization
set_option autoImplicit false

/-- An actual general virtual Read transports a different physical root's
snapshot and all current runtime row facts. Separation is derived internally;
no successful callback or final permission certificate is an input. Static
support/coverage data come from the initial S01 authorization. -/
theorem after_virtual (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root other : UniIndex) (rootMember : root ∈ tree.roots.toList)
    (otherMember : other ∈ tree.roots.toList) (different : root ≠ other)
    (position : Nat) (maximum : Option BorTag) (virtual : position ≠ 0)
    (support : GeneralBorrowWildcardControlStack.Support tree root)
    (covers : ∀ index, support.contains index → GeneralBorrowExposureCardinality.Covers tree.nodes root index)
    (snapshot : Snapshot tree initial protections root position maximum .Read support.contains)
    (otherSupport : UniIndex → Prop)
    (otherPresent : ∀ index, otherSupport index → ∃ node, tree.nodes.get index = some node)
    (otherCovers : ∀ index, otherSupport index → GeneralBorrowExposureCardinality.Covers tree.nodes other index)
    (otherPosition : Nat) (otherMaximum : Option BorTag)
    (otherSnapshot : Snapshot tree initial protections other otherPosition otherMaximum .Read otherSupport)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree initial) :
    let result := tree.performWildcardAccessAt initial root maximum .Read protections true
    result.status = .Completed ∧
    GeneralBorrowExposedNonleafState.ReadFrame initial result.location ∧
    GeneralBorrowWildcardPrimaryReadWitness.PointwiseReadFrame tree protections initial result.location ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree result.location protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree result.location ∧
    (∀ query, tree.nodes.get query = none → result.location.perms.get query = initial.perms.get query) ∧
    Snapshot tree result.location protections root position maximum .Read support.contains ∧
    Snapshot tree result.location protections other otherPosition otherMaximum .Read otherSupport := by
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨status, counters, self, pointwise, coherentAfter, outside, profileAfter, possibleAfter, vacant⟩ :=
    GeneralBorrowSnapshotVirtualReadAccess.access_runtime tree initial protections root position maximum virtual
      support snapshot depth forest coherent profile possible
  have transported := GeneralBorrowSnapshotReadTransport.transport_other tree initial _ protections formed
    root other rootMember otherMember different support.contains otherSupport covers otherPresent otherCovers
    otherPosition otherMaximum otherSnapshot counters outside
  exact ⟨status, counters, pointwise, coherentAfter, profileAfter, possibleAfter, vacant, self, transported⟩

end DuplicatePrefix.GeneralBorrowSnapshotReadOtherRoot
