import duplicate_prefix.GeneralBorrowReadNoMaximumWriteFrame
import duplicate_prefix.GeneralBorrowSnapshotReadTransport
namespace DuplicatePrefix.GeneralBorrowSnapshotAnyKindTransport
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization
open GeneralBorrowWildcardVirtualLeaf (effective)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def CounterFrame (before after : LocationTree) (kind : AccessKind) : Prop :=
  ∀ query, GeneralBorrowExposureCardinality.counter after.exposedCache query kind = GeneralBorrowExposureCardinality.counter before.exposedCache query kind

theorem relation_frame (before after : LocationTree) (kind : AccessKind) (frame : CounterFrame before after kind)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (position : Nat) :
    relation after root index node maximum kind position = relation before root index node maximum kind position := by
  have counts (query : UniIndex) : GeneralBorrowWildcardRelatednessBounds.count after.exposedCache query kind =
      GeneralBorrowWildcardRelatednessBounds.count before.exposedCache query kind := by
    cases kind <;> exact congrArg UInt16.toNat (frame query)
  simp only [relation,counts]

theorem transport (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (support : UniIndex → Prop)
    (snapshot : Snapshot tree before protections root position maximum kind support)
    (counters : CounterFrame before after kind)
    (slots : ∀ index, support index → after.perms.get index = before.perms.get index) :
    Snapshot tree after protections root position maximum kind support := by
  refine ⟨?_,?_⟩
  · intro index node included present
    rw [relation_frame before after kind counters]
    change Scalar (effective after index node) kind _ _
    simpa only [effective,slots index included] using snapshot.scalar index node included present
  · intro physical
    obtain ⟨index,node,included,present,witness⟩ := snapshot.witness physical
    exact ⟨index,node,included,present,by simpa only [Supports,slots index included] using witness⟩

/-- Any-kind authorization of a different physical root survives a no-cutoff
Read when its actual counter and outside-slot frames hold. This is an internal
transport lemma; operational users derive those frames from real callbacks. -/
theorem authorization_other (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (root other : UniIndex) (rootMember : root ∈ tree.roots.toList) (otherMember : other ∈ tree.roots.toList) (different : root ≠ other)
    (support otherSupport : UniIndex → Prop)
    (covers : ∀ index, support index → GeneralBorrowExposureCardinality.Covers tree.nodes root index)
    (position : Nat) (kind : AccessKind)
    (authorization : DuplicatePrefixResidualSupportAuthorization.Authorization tree before protections other position none kind otherSupport)
    (beforeCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree before protections)
    (afterCoherent : GeneralBorrowExposureCardinality.LocationCoherent tree after protections) (short : tree.nodes.size < 65536)
    (counters : CounterFrame before after kind)
    (outside : ∀ index, ¬support index → after.perms.get index = before.perms.get index) :
    DuplicatePrefixResidualSupportAuthorization.Authorization tree after protections other position none kind otherSupport := by
  have initial := DuplicatePrefixResidualInitialSnapshot.snapshot tree before protections other position none kind otherSupport authorization beforeCoherent short
  have current : Snapshot tree after protections other position none kind otherSupport := by
    apply transport tree before after protections other position none kind otherSupport initial counters
    intro index included
    apply outside index
    intro inside
    obtain ⟨node,present⟩ := authorization.present index included
    exact GeneralBorrowSnapshotReadTransport.covers_disjoint tree before protections formed root other index node present rootMember otherMember different
      (covers index inside) (authorization.covers index included)
  exact DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree after protections other position none kind otherSupport current
    authorization.rooted authorization.present authorization.children authorization.covers afterCoherent short
    (fun removed legal => DuplicatePrefixResidualSupportAuthorization.no_maximum_removal_empty tree after protections kind removed legal)

end DuplicatePrefix.GeneralBorrowSnapshotAnyKindTransport
