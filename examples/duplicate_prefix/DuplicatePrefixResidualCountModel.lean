import duplicate_prefix.DuplicatePrefixResidualSupportAuthorization
import duplicate_prefix.GeneralBorrowExposureLevelUpdate

namespace DuplicatePrefix.DuplicatePrefixResidualCountModel
open Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false

/-- Initial contribution strengths with the finite removal mask applied. This
is an internal algebraic model, not an assumed successful execution state. -/
def levels (initial : LocationTree) (protections : ProtectedTags) (removed : List UniIndex) :
    UniIndex → TreeNode → WildcardAccessLevel := fun index node =>
  if removed.contains index then .None else effective initial protections index node

theorem count_as_cardinality (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (kind : AccessKind) (removed : List UniIndex) (query : UniIndex) :
    residualCount tree initial protections kind removed query =
      cardinality tree.nodes (levels initial protections removed) query kind := by
  unfold residualCount cardinality
  rw [List.filter_filter]
  apply congrArg List.length
  apply List.filter_congr
  intro row member
  by_cases masked : row.1 ∈ removed <;> cases kind <;>
    simp [contributes, levels, masked, supports,
      GeneralBorrowExposureAncestorFold.supportsRead, GeneralBorrowExposureAncestorFold.supportsWrite]

theorem levels_cons (initial : LocationTree) (protections : ProtectedTags)
    (removed : List UniIndex) (index : UniIndex) :
    levels initial protections (index :: removed) =
      GeneralBorrowExposureLevelUpdate.replace (levels initial protections removed) index .None := by
  funext query node
  by_cases equal : query = index
  · subst query
    simp [levels, GeneralBorrowExposureLevelUpdate.replace]
  · simp [levels, GeneralBorrowExposureLevelUpdate.replace, equal]

/-- One removed supporter subtracts exactly its contribution at each ancestor;
no machine-width subtraction, cache outcome or visitor order is assumed. -/
theorem count_cons_balance (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (kind : AccessKind) (removed : List UniIndex) (query index : UniIndex)
    (node : TreeNode) (present : tree.nodes.get index = some node) :
    residualCount tree initial protections kind (index :: removed) query +
      (if contributes tree.nodes (levels initial protections removed) query kind (index, node) then 1 else 0) =
    residualCount tree initial protections kind removed query := by
  rw [count_as_cardinality, count_as_cardinality, levels_cons]
  have balance := GeneralBorrowExposureLevelUpdate.cardinality_balance tree.nodes
    (levels initial protections removed) index node present .None query kind
  cases kind <;> simpa [contributes, GeneralBorrowExposureLevelUpdate.replace, supports,
    GeneralBorrowExposureAncestorFold.supportsRead, GeneralBorrowExposureAncestorFold.supportsWrite] using balance

theorem removal_cons (tree : BorrowTree) (initial : LocationTree) (protections : ProtectedTags)
    (maximum : Option BorTag) (kind : AccessKind) (removed : List UniIndex)
    (legal : Removal tree initial protections maximum kind removed)
    (index : UniIndex) (fresh : index ∉ removed) (node : TreeNode)
    (present : tree.nodes.get index = some node)
    (allowed : removable initial protections maximum kind index node = true) :
    Removal tree initial protections maximum kind (index :: removed) := by
  refine ⟨List.nodup_cons.mpr ⟨fresh, legal.distinct⟩, ?_⟩
  intro query member
  rcases List.mem_cons.mp member with same | old
  · subst query
    exact ⟨node, present, allowed⟩
  · exact legal.allowed query old

/-- Equality of actual current-kind support with the masked initial support.
Other access-kind counters may change. This invariant is established locally
when simulating actual transitions; it is not part of the call-time contract. -/
def Matches (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (kind : AccessKind) (removed : List UniIndex) : Prop :=
  ∀ index node, tree.nodes.get index = some node → node.isExposed = true →
    supports (effective current protections index node) kind =
      supports (levels initial protections removed index node) kind

theorem counts_match (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (kind : AccessKind) (removed : List UniIndex) (matching : Matches tree initial current protections kind removed)
    (query : UniIndex) :
    cardinality tree.nodes (effective current protections) query kind =
      residualCount tree initial protections kind removed query := by
  rw [count_as_cardinality]
  unfold cardinality
  apply congrArg List.length
  apply List.filter_congr
  intro row member
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
  cases exposed : row.2.isExposed with
  | false => simp [contributes, exposed]
  | true => simp only [contributes, exposed, matching row.1 row.2 present exposed]

/-- Coherence and the contribution invariant derive exact residual cache
counts, including the Nat virtual-root classification used by Lean. -/
theorem relation_matches (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (kind : AccessKind) (removed : List UniIndex) (matching : Matches tree initial current protections kind removed)
    (coherent : LocationCoherent tree current protections) (short : tree.nodes.size < 65536)
    (root index : UniIndex) (node : TreeNode) (maximum : Option BorTag) (position : Nat) :
    DuplicatePrefixCallbackAuthorization.relation current root index node maximum kind position =
      residualRelation tree initial protections root index node maximum kind position removed := by
  have counts (query : UniIndex) : GeneralBorrowWildcardRelatednessBounds.count current.exposedCache query kind =
      residualCount tree initial protections kind removed query := by
    have exactCount := (nat_exact current.exposedCache tree.nodes (effective current protections) coherent short query kind).trans
      (counts_match tree initial current protections kind removed matching query)
    cases kind <;> exact exactCount
  simp only [DuplicatePrefixCallbackAuthorization.relation, residualRelation, counts]

end DuplicatePrefix.DuplicatePrefixResidualCountModel
