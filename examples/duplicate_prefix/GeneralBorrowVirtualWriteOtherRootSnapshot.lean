import duplicate_prefix.GeneralBorrowRootLocalCounterFrame
import duplicate_prefix.DuplicatePrefixResidualVirtualWriteAccess
import duplicate_prefix.DuplicatePrefixResidualInitialSnapshot
import duplicate_prefix.DuplicatePrefixResidualPrimaryWriteAccess
namespace DuplicatePrefix.GeneralBorrowVirtualWriteOtherRootSnapshot
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixResidualSupportAuthorization
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A real virtual Write preserves an arbitrary other physical root's Read or
Write Snapshot, for every cutoff. Global Read/Write counter equality is neither
assumed nor claimed; graph-derived root separation and actual coherent caches
supply the needed root-local equalities. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root other : UniIndex) (rootMember : root ∈ tree.roots.toList)
    (otherMember : other ∈ tree.roots.toList) (different : root ≠ other)
    (position otherPosition : Nat) (maximum : Option BorTag) (virtual : position ≠ 0)
    (support otherSupport : UniIndex → Prop) (kind : AccessKind)
    (authorization : Authorization tree initial protections root position maximum .Write support)
    (otherAuthorization : Authorization tree initial protections other otherPosition maximum kind otherSupport)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root maximum .Write protections true
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    Snapshot tree result.location protections other otherPosition maximum kind otherSupport := by
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨forest⟩ := formed.forest initial protections
  obtain ⟨completed,removed,legal,matching,afterCoherent,outside⟩ :=
    DuplicatePrefixResidualVirtualWriteAccess.of_authorization tree initial protections root position maximum virtual support authorization depth forest coherent short
  have snapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections other otherPosition maximum kind otherSupport otherAuthorization coherent short
  exact ⟨completed,afterCoherent,GeneralBorrowRootLocalCounterFrame.snapshot_other tree initial _ protections formed root other rootMember otherMember different support otherSupport authorization.covers otherAuthorization.covers otherAuthorization.present otherPosition maximum kind snapshot coherent afterCoherent outside⟩

/-- The actual primary no-cutoff Write also transports every other physical
root's snapshot, without asserting global Read-counter preservation. -/
theorem primary (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root other : UniIndex) (rootMember : root ∈ tree.roots.toList)
    (otherMember : other ∈ tree.roots.toList) (different : root ≠ other)
    (otherPosition : Nat) (support otherSupport : UniIndex → Prop) (kind : AccessKind)
    (authorization : Authorization tree initial protections root 0 none .Write support)
    (otherAuthorization : Authorization tree initial protections other otherPosition none kind otherSupport)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections)
    (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt initial root none .Write protections false
    result.status = .Completed ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
    Snapshot tree result.location protections other otherPosition none kind otherSupport := by
  obtain ⟨completed,matching,afterCoherent,outside⟩ :=
    DuplicatePrefixResidualPrimaryWriteAccess.access tree initial protections formed root support authorization coherent short
  have snapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree initial protections other otherPosition none kind otherSupport otherAuthorization coherent short
  exact ⟨completed,afterCoherent,GeneralBorrowRootLocalCounterFrame.snapshot_other tree initial _ protections formed root other rootMember otherMember different support otherSupport authorization.covers otherAuthorization.covers otherAuthorization.present otherPosition none kind snapshot coherent afterCoherent outside⟩
end DuplicatePrefix.GeneralBorrowVirtualWriteOtherRootSnapshot
