import duplicate_prefix.DuplicatePrefixResidualReadWriteEffects

namespace DuplicatePrefix.DuplicatePrefixResidualComposition
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposureCardinality DuplicatePrefixResidualSupportAuthorization
open DuplicatePrefixResidualCountModel DuplicatePrefixResidualReadWriteEffects
set_option autoImplicit false

/-- Successive support masks compose by finite list append; order and duplicate
entries do not affect this contribution identity. No execution is assumed. -/
theorem matches_compose (tree : BorrowTree) (initial middle finalLocation : LocationTree)
    (protections : ProtectedTags) (first second : List UniIndex)
    (before : Matches tree initial middle protections .Write first)
    (after : Matches tree middle finalLocation protections .Write second) :
    Matches tree initial finalLocation protections .Write (first ++ second) := by
  intro index node present exposed
  have one := before index node present exposed
  have two := after index node present exposed
  by_cases firstMember : index ∈ first <;> by_cases secondMember : index ∈ second <;>
    simp_all [levels, supports, GeneralBorrowExposureAncestorFold.supportsWrite]

/-- Applying a later mask to current strengths is exactly the combined mask. -/
theorem masked_supports (tree : BorrowTree) (initial current : LocationTree)
    (protections : ProtectedTags) (first second : List UniIndex)
    (matching : Matches tree initial current protections .Write first)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (exposed : node.isExposed = true) :
    supports (levels current protections second index node) .Write =
      supports (levels initial protections (first ++ second) index node) .Write := by
  have before := matching index node present exposed
  by_cases firstMember : index ∈ first <;> by_cases secondMember : index ∈ second <;>
    simp_all [levels, supports, GeneralBorrowExposureAncestorFold.supportsWrite]

/-- Current residual counts agree with the combined original mask. -/
theorem count_append (tree : BorrowTree) (initial current : LocationTree)
    (protections : ProtectedTags) (first second : List UniIndex)
    (matching : Matches tree initial current protections .Write first) (query : UniIndex) :
    residualCount tree current protections .Write second query =
      residualCount tree initial protections .Write (first ++ second) query := by
  rw [count_as_cardinality, count_as_cardinality]
  unfold cardinality
  apply congrArg List.length
  apply List.filter_congr
  intro row member
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp member
  cases exposed : row.2.isExposed with
  | false => simp [contributes, exposed]
  | true => simp only [contributes, exposed,
      masked_supports tree initial current protections first second matching row.1 row.2 present exposed]

/-- The current entry/exit classifier is the initial combined-mask classifier. -/
theorem relation_append (tree : BorrowTree) (initial current : LocationTree)
    (protections : ProtectedTags) (maximum : Option BorTag) (first second : List UniIndex)
    (matching : Matches tree initial current protections .Write first)
    (root index : UniIndex) (node : TreeNode) (position : Nat) :
    residualRelation tree current protections root index node maximum .Write position second =
      residualRelation tree initial protections root index node maximum .Write position (first ++ second) := by
  simp only [residualRelation, count_append tree initial current protections first second matching]

/-- A current legal supporter removal was already removable initially when
Read preserved the origin of every remaining supporting permission. -/
theorem removable_origin (tree : BorrowTree) (initial current : LocationTree)
    (protections : ProtectedTags) (maximum : Option BorTag)
    (origin : Origin tree initial current protections) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node)
    (allowed : removable current protections maximum .Write index node = true) :
    removable initial protections maximum .Write index node = true := by
  have parts := allowed
  simp only [removable, Bool.and_eq_true] at parts
  rcases parts with ⟨⟨⟨exposed, above⟩, supported⟩, loses⟩
  have same := origin index node present exposed supported
  simpa only [removable, effective, same] using allowed

/-- A supporter still eligible for a later removal cannot belong to the first
mask. The conclusion follows from actual support matching, not from an
unvisited-node assumption. -/
theorem masks_disjoint (tree : BorrowTree) (initial current : LocationTree)
    (protections : ProtectedTags) (maximum : Option BorTag) (first second : List UniIndex)
    (matching : Matches tree initial current protections .Write first)
    (legal : Removal tree current protections maximum .Write second) :
    ∀ index ∈ first, index ∉ second := by
  intro index firstMember secondMember
  obtain ⟨node, present, allowed⟩ := legal.allowed index secondMember
  simp only [removable, Bool.and_eq_true] at allowed
  rcases allowed with ⟨⟨⟨exposed, above⟩, supported⟩, loses⟩
  have equality := matching index node present exposed
  rw [supported] at equality
  simp [levels, firstMember, supports, GeneralBorrowExposureAncestorFold.supportsWrite] at equality

/-- The complete later removal mask transfers back to the original row.
Legality and freshness are derived from Origin and Matches; neither is added
as an operation-success or post-permission precondition of the final call. -/
theorem removal_append (tree : BorrowTree) (initial current : LocationTree)
    (protections : ProtectedTags) (maximum : Option BorTag) (first second : List UniIndex)
    (firstLegal : Removal tree initial protections maximum .Write first)
    (secondLegal : Removal tree current protections maximum .Write second)
    (matching : Matches tree initial current protections .Write first)
    (origin : Origin tree initial current protections) :
    Removal tree initial protections maximum .Write (first ++ second) := by
  refine ⟨List.nodup_append.mpr ⟨firstLegal.distinct, secondLegal.distinct, ?_⟩, ?_⟩
  · intro left leftMember right rightMember equal
    subst right
    exact masks_disjoint tree initial current protections maximum first second matching secondLegal left leftMember rightMember
  · intro index member
    rcases List.mem_append.mp member with earlier | later
    · exact firstLegal.allowed index earlier
    · obtain ⟨node, present, allowed⟩ := secondLegal.allowed index later
      exact ⟨node, present, removable_origin tree initial current protections maximum origin index node present allowed⟩

end DuplicatePrefix.DuplicatePrefixResidualComposition
