import duplicate_prefix.DuplicatePrefixResidualSupportAuthorization

namespace DuplicatePrefix.S05ResidualQueryCoverage
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false

/-- The conservative pair quantifier adds no condition when initial raw data
admits only the empty removal. This concerns query authorization alone; rooted
support, graph, permissions and ordinary-valid coverage remain separate. -/
theorem queries_iff_initial
    (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind)
    (support : UniIndex → Prop)
    (empty : ∀ removed, Removal tree location protections maximum kind removed → removed = []) :
    (∀ before after, Removal tree location protections maximum kind before →
      Removal tree location protections maximum kind after →
      (∀ index ∈ before, index ∈ after) →
      ∀ index node, support index → tree.nodes.get index = some node → index ∉ after →
        DuplicatePrefixCallbackVisitAuthorization.Authorized
          ((location.perms.get index).getD node.defaultLocationState) kind (protections.contains node.tag)
          (residualRelation tree location protections root index node maximum kind position before)
          (residualRelation tree location protections root index node maximum kind position after)) ↔
    (∀ index node, support index → tree.nodes.get index = some node →
        DuplicatePrefixCallbackVisitAuthorization.Authorized
          ((location.perms.get index).getD node.defaultLocationState) kind (protections.contains node.tag)
          (residualRelation tree location protections root index node maximum kind position [])
          (residualRelation tree location protections root index node maximum kind position [])) := by
  constructor
  · intro queries index node supported present
    exact queries [] [] (empty_removal tree location protections maximum kind)
      (empty_removal tree location protections maximum kind) (by simp) index node supported present (by simp)
  · intro initial before after legalBefore legalAfter _ index node supported present _
    rw [empty before legalBefore,empty after legalAfter]
    exact initial index node supported present

/-- Read never removes a contributor, for arbitrary initial permissions, tags,
protections and maximum. No order, coherence or operation outcome is needed. -/
theorem read_queries_iff_initial
    (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (support : UniIndex → Prop) :
    (∀ before after, Removal tree location protections maximum .Read before →
      Removal tree location protections maximum .Read after →
      (∀ index ∈ before, index ∈ after) →
      ∀ index node, support index → tree.nodes.get index = some node → index ∉ after →
        DuplicatePrefixCallbackVisitAuthorization.Authorized
          ((location.perms.get index).getD node.defaultLocationState) .Read (protections.contains node.tag)
          (residualRelation tree location protections root index node maximum .Read position before)
          (residualRelation tree location protections root index node maximum .Read position after)) ↔
    (∀ index node, support index → tree.nodes.get index = some node →
        DuplicatePrefixCallbackVisitAuthorization.Authorized
          ((location.perms.get index).getD node.defaultLocationState) .Read (protections.contains node.tag)
          (residualRelation tree location protections root index node maximum .Read position [])
          (residualRelation tree location protections root index node maximum .Read position [])) :=
  queries_iff_initial tree location protections root position maximum .Read support
    (fun removed legal => read_removal_empty tree location protections maximum removed legal)

/-- The no-maximum case also has no pairwise-removal strengthening, for both
access kinds, independently of numeric cache bounds and parent-tag order. -/
theorem no_maximum_queries_iff_initial
    (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (kind : AccessKind) (support : UniIndex → Prop) :
    (∀ before after, Removal tree location protections none kind before →
      Removal tree location protections none kind after →
      (∀ index ∈ before, index ∈ after) →
      ∀ index node, support index → tree.nodes.get index = some node → index ∉ after →
        DuplicatePrefixCallbackVisitAuthorization.Authorized
          ((location.perms.get index).getD node.defaultLocationState) kind (protections.contains node.tag)
          (residualRelation tree location protections root index node none kind position before)
          (residualRelation tree location protections root index node none kind position after)) ↔
    (∀ index node, support index → tree.nodes.get index = some node →
        DuplicatePrefixCallbackVisitAuthorization.Authorized
          ((location.perms.get index).getD node.defaultLocationState) kind (protections.contains node.tag)
          (residualRelation tree location protections root index node none kind position [])
          (residualRelation tree location protections root index node none kind position [])) :=
  queries_iff_initial tree location protections root position none kind support
    (fun removed legal => no_maximum_removal_empty tree location protections kind removed legal)

end DuplicatePrefix.S05ResidualQueryCoverage
