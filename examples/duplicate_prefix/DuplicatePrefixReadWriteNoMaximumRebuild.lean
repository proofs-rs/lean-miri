import duplicate_prefix.DuplicatePrefixReadWriteAuthorizationRebuild
namespace DuplicatePrefix.DuplicatePrefixReadWriteNoMaximumRebuild
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality DuplicatePrefixCallbackAuthorization
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixResidualCountModel
open GeneralBorrowSnapshotReadTransfer
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem support_allows (level : WildcardAccessLevel) : supports level .Write = level.allows .Write := by
  cases level <;> rfl

/-- With no tag maximum every legal Write mask is empty. Read scalar transfer
and exact contribution matching then reconstruct Write authorization for ANY
root position, including its genuine physical-root supporting witness. -/
theorem rebuild (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (rootPosition : Nat) (support : UniIndex → Prop)
    (old : Authorization tree initial protections root rootPosition none .Write support)
    (coherent : LocationCoherent tree initial protections) (short : tree.nodes.size < 65536)
    (removed : List UniIndex) (legal : Removal tree initial protections none .Write removed)
    (matching : Matches tree initial current protections .Write removed)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current)
    (transfer : Global tree initial current protections root rootPosition none support) :
    Authorization tree current protections root rootPosition none .Write support := by
  have removedEmpty := no_maximum_removal_empty tree initial protections .Write removed legal
  subst removed
  refine ⟨old.rooted,old.present,old.children,old.covers,?_,?_,?_⟩
  · intro index node included present
    exact possible index node present
  · intro before after legalBefore legalAfter subset index node included present notRemoved
    have beforeEmpty := no_maximum_removal_empty tree current protections .Write before legalBefore
    have afterEmpty := no_maximum_removal_empty tree current protections .Write after legalAfter
    subst before
    subst after
    have equality := DuplicatePrefixResidualComposition.relation_append tree initial current protections none [] [] matching root index node rootPosition
    simp only [List.nil_append] at equality
    rw [equality]
    have empty := empty_removal tree initial protections none .Write
    have authorized := old.queries [] [] empty empty (by intro query member; cases member) index node included present (by simp)
    have guards := DuplicatePrefixReadWriteAuthorizationRebuild.masked_guards tree initial protections root index node none rootPosition [] [] coherent short (old.covers index included)
    exact transfer index node included present _ _ guards authorized
  · intro physical
    obtain ⟨index,node,included,present,exposed,allowed,cutoff⟩ := old.witness physical
    refine ⟨index,node,included,present,exposed,?_,rfl⟩
    have equality := matching index node present exposed
    have supportEq : supports (effective current protections index node) .Write =
        supports (effective initial protections index node) .Write := by simpa [levels] using equality
    change (effective current protections index node).allows .Write = true
    rw [←support_allows,supportEq,support_allows]
    exact allowed
end DuplicatePrefix.DuplicatePrefixReadWriteNoMaximumRebuild
