import duplicate_prefix.S03EmptyPopFactsAuthorization
import duplicate_prefix.S02SameDestinationAcceptedMutableForeign
import duplicate_prefix.GeneralBorrowSharedAuthorizationGeometry
namespace DuplicatePrefix.S02WildcardSameDestinationRootCallback
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixResidualSupportAuthorization DuplicatePrefixCallbackAuthorization GeneralBorrowExposureCardinality
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
/-- A new hidden leaf has zero residual count for every permitted removal set. -/
theorem count_zero (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (location : LocationTree)
    (protections : ProtectedTags) (kind : AccessKind) (removed : List UniIndex) :
    residualCount tree location protections kind removed index = 0 := by
  have empty := S03EmptyPopFactsAuthorization.leaf_cardinality tree location protections graph index node present leaf hidden kind
  unfold cardinality at empty
  have filtered := List.eq_nil_of_length_eq_zero empty
  simp only [residualCount,filtered,List.filter_nil,List.length_nil]

/-- Every callback to the new virtual hidden root is truly Foreign, including
when the old destination cutoff does not exclude its tag. -/
theorem authorization (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false)
    (location : LocationTree) (protections : ProtectedTags)
    (state : (location.perms.get index).getD node.defaultLocationState = ⟨.ReservedFrz false,false,.None⟩)
    (position : Nat) (virtual : 0 < position) (maximum : Option BorTag) (kind : AccessKind) :
    Authorization tree location protections index position maximum kind (fun query => query = index) := by
  have residual (removed : List UniIndex) :
      residualRelation tree location protections index index node maximum kind position removed = some .ForeignAccess := by
    unfold residualRelation
    rw [count_zero tree graph index node present leaf hidden location protections kind removed]
    have notzero : (position != 0) = true := by simp [Nat.ne_of_gt virtual]
    rw [notzero]
    cases aboveMaximum node maximum <;> rfl
  refine ⟨rfl,?_,?_,?_,?_,?_,?_⟩
  · intro query same
    subst query
    exact ⟨node,present⟩
  · intro query value same found child member
    subst query
    have equal := Option.some.inj (found.symm.trans present)
    subst value
    rw [leaf] at member
    cases member
  · intro query same
    subst query
    exact GeneralBorrowSharedAuthorizationGeometry.covers_of_path tree (Classical.choice graph.depth) index index (.refl index node present)
  · intro query value same found
    subst query
    have equal := Option.some.inj (found.symm.trans present)
    subst value
    rw [state]
    rfl
  · intro before after _legalBefore _legalAfter _subset query value same found _retained
    subst query
    have equal := Option.some.inj (found.symm.trans present)
    subst value
    rw [state,residual before,residual after]
    exact S02SameDestinationAcceptedMutableForeign.query .None kind (protections.contains node.tag)
  · intro impossible
    omega
end DuplicatePrefix.S02WildcardSameDestinationRootCallback
