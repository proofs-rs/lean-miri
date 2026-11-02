import duplicate_prefix.GeneralBorrowNormalOtherCallbackFrame
import duplicate_prefix.GeneralBorrowSnapshotVirtualReadAccess
import duplicate_prefix.DuplicatePrefixVirtualWriteBothClosure
namespace DuplicatePrefix.GeneralBorrowNormalOtherCallback
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowForest
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- An actual other-root virtual Read OR Write retains the selected concrete
Normal authorization for BOTH scalar kinds. Source completion and the
outside-slot frame are derived internally from the raw callback candidate.
The normal component is canonicalized, so an arbitrary larger initial
certificate is accepted. No leaf, SIFA profile, ParentTagOrder, or operation-
success/frame input is added for this selected-component transport. -/
theorem after_virtual (tree : BorrowTree) (before : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected other : UniIndex) (anchorNode : TreeNode)
    (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree before protections anchor)
    (rootPath : ((source_normal_projection tree before protections).topology.ancestorPath anchor.toNat).getLast? = some selected.toNat)
    (otherMember : other ∈ tree.roots.toList) (different : selected ≠ other)
    (position : Nat) (maximum : Option BorTag) (virtual : position ≠ 0) (kind : AccessKind) (support : UniIndex → Prop)
    (callback : Authorization tree before protections other position maximum kind support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree before protections) (short : tree.nodes.size < 65536) :
    let result := tree.performWildcardAccessAt before other maximum kind protections true
    result.status = .Completed ∧ GeneralBorrowExposureCardinality.LocationCoherent tree result.location protections ∧
      (∃ next : DuplicatePrefixBorrowAuthorization.Normal tree result.location protections anchor,
        next.component.support = Desc (source_normal_projection tree before protections).topology selected.toNat) ∧
      (∀ query, ¬support query → result.location.perms.get query = before.perms.get query) := by
  obtain ⟨forest⟩ := formed.forest before protections
  obtain ⟨depth⟩ := formed.depth
  cases kind with
  | Read =>
    obtain ⟨done,_,_,_,afterCoherent,outside⟩ := GeneralBorrowSnapshotVirtualReadAccess.of_authorization_frame tree before protections other position maximum
      virtual support callback depth forest coherent short
    exact ⟨done,afterCoherent,GeneralBorrowNormalOtherCallbackFrame.transport tree before _ protections formed anchor selected other anchorNode anchorPresent
      normal rootPath otherMember different support callback.present callback.covers outside,outside⟩
  | Write =>
    obtain ⟨done,_,_,_,_,afterCoherent,outside⟩ := DuplicatePrefixVirtualWriteBothClosure.of_authorization tree before protections other position maximum
      virtual support callback depth forest coherent short
    exact ⟨done,afterCoherent,GeneralBorrowNormalOtherCallbackFrame.transport tree before _ protections formed anchor selected other anchorNode anchorPresent
      normal rootPath otherMember different support callback.present callback.covers outside,outside⟩
end DuplicatePrefix.GeneralBorrowNormalOtherCallback
