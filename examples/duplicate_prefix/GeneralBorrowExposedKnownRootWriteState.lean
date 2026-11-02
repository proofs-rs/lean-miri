import duplicate_prefix.GeneralBorrowExposedKnownRootState
import duplicate_prefix.GeneralBorrowExposedConditionalAccessSupport
import duplicate_prefix.GeneralBorrowWildcardSubtreeInvariant
import duplicate_prefix.GeneralBorrowExposedVirtualSchedule

namespace DuplicatePrefix.GeneralBorrowExposedKnownRootWriteState
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective materialized onlyForeign)
open GeneralBorrowWildcardSubtreeState (write write_same write_other)
open GeneralBorrowExposureCardinality (counter)
set_option maxRecDepth 65536
set_option maxHeartbeats 200000

open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]

def zero (location : LocationTree) (index : UniIndex) : Bool :=
  GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Write == 0

def Profile (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) : Prop :=
  ∀ index node, area.support index → tree.nodes.get index = some node →
    GeneralBorrowExposedConditionalWritePermissions.Condition (zero location index) (effective location index node) (protections.contains node.tag)

open GeneralBorrowExposedNonleafState (updated updated_other)
def WriteFrame (before after : LocationTree) : Prop :=
  ∀ query, counter after.exposedCache query .Write = counter before.exposedCache query .Write

def foreign (initial : LocationTree) (index : UniIndex) (node : TreeNode) (maximum : Option Miri.Memory.BorTag) : Bool :=
  onlyForeign node maximum || GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write == 0

def related (initial : LocationTree) (root index : UniIndex) : WildcardAccessRelatedness :=
  if GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache root .Write == GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write then .LocalAccess
  else if GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write == 0 then .ForeignAccess else .EitherAccess


structure Data (tree : BorrowTree) (initial : LocationTree) (root : UniIndex) (protections : ProtectedTags) where
  support : UniIndex → Prop
  rooted : support root
  present : ∀ index, support index → ∃ node, tree.nodes.get index = some node
  children : ∀ index node, support index → tree.nodes.get index = some node →
    ∀ child ∈ node.children.toList, support child
  covers : ∀ index, support index → GeneralBorrowExposureCardinality.Covers tree.nodes root index
  coherent : GeneralBorrowExposureCardinality.LocationCoherent tree initial protections
  short : tree.nodes.size < 65536
  depth : GeneralBorrowExposure.ParentDepth tree.nodes
  included : ∀ index,support index → area.support index
  profile : Profile tree initial protections

theorem classify {tree initial root protections} (data : Data tree initial root protections)
    (location : LocationTree) (frame : WriteFrame initial location) (index : UniIndex) (node : TreeNode)
    (supported : data.support index) (maximum : Option Miri.Memory.BorTag) :
    location.exposedCache.accessRelatedness root index .Write true (onlyForeign node maximum) =
      some (if foreign initial index node maximum then .ForeignAccess else .EitherAccess) := by
  have countEq : ∀ query, GeneralBorrowWildcardRelatednessBounds.count location.exposedCache query .Write =
      GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache query .Write :=
    fun query => congrArg UInt16.toNat (frame query)
  have bounded := GeneralBorrowExposureCardinality.dominates initial.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective initial protections) data.coherent data.short root index (data.covers index supported) .Write
  change GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write ≤ GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache root .Write at bounded
  rw [GeneralBorrowWildcardRelatednessBounds.virtual_classify _ _ _ _ _ (by simpa only [countEq] using bounded)]
  simp only [countEq,foreign]
  rfl


theorem zero_frame (before after : LocationTree) (frame : WriteFrame before after) (query : UniIndex) : zero after query = zero before query := by
  unfold zero
  have eq : GeneralBorrowWildcardRelatednessBounds.count after.exposedCache query .Write = GeneralBorrowWildcardRelatednessBounds.count before.exposedCache query .Write := congrArg UInt16.toNat (frame query)
  rw [eq]

theorem foreign_compatible (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (frame : WriteFrame initial current) (profile : Profile tree current protections)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (inArea : area.support index)
    (isZero : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write = 0) :
    GeneralBorrowExposedConditionalWritePermissions.Compatible (effective current index node) .ForeignAccess (protections.contains node.tag) := by
  have good := profile index node inArea present
  have eq : zero current index = true := by rw [zero_frame initial current frame index];simp [zero,isZero]
  simpa only [GeneralBorrowExposedConditionalWritePermissions.Condition,eq,ite_true] using good

theorem local_compatible (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (frame : WriteFrame initial current) (profile : Profile tree current protections)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (inArea : area.support index)
    (nonzero : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write ≠ 0) :
    GeneralBorrowExposedConditionalWritePermissions.Compatible (effective current index node) .LocalAccess (protections.contains node.tag) := by
  have good := profile index node inArea present
  have eq : zero current index = false := by rw [zero_frame initial current frame index];simp [zero,nonzero]
  simpa only [GeneralBorrowExposedConditionalWritePermissions.Condition,eq,Bool.false_eq_true,ite_false] using good

theorem materialized_profile (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (node : TreeNode)
    (protections : ProtectedTags) (present : tree.nodes.get root = some node) (initial : Profile tree location protections) :
    Profile tree (materialized location root node) protections := by
  intro query queryNode inArea found
  rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree location root node present query queryNode found]
  exact initial query queryNode inArea found

theorem updated_frame (tree : BorrowTree) (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (protections : ProtectedTags) (recorded next : LocationState) (delta : PermTransition)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (present : tree.nodes.get index = some node)
    (support : node.isExposed = true → GeneralBorrowExposedConditionalWritePermissions.support next (protections.contains node.tag) =
      GeneralBorrowExposedConditionalWritePermissions.support (effective location index node) (protections.contains node.tag)) :
    WriteFrame location (updated tree location index node protections recorded next delta) := by
  intro query
  unfold updated
  dsimp only
  split
  · have exposed : node.isExposed = true := by
      have condition := ‹(node.isExposed && !delta.isNoop) = true›
      simp only [Bool.and_eq_true] at condition
      exact condition.1
    rw [GeneralBorrowExposurePointwise.update_counter _ _ depth index node present]
    rw [show GeneralBorrowExposureCardinality.supports (next.permission.strongestAllowedLocalAccess (protections.contains node.tag)) .Write =
      GeneralBorrowExposureCardinality.supports ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)) .Write from support exposed]
    cases GeneralBorrowExposureCardinality.supports
      ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)) .Write <;>
      simp [GeneralBorrowExposureAncestorFold.delta]
  · rfl

theorem updated_profile (tree : BorrowTree) (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (protections : ProtectedTags) (recorded next : LocationState) (delta : PermTransition)
    (present : tree.nodes.get index = some node) (initial : Profile tree location protections)
    (frame : WriteFrame location (updated tree location index node protections recorded next delta))
    (good : GeneralBorrowExposedConditionalWritePermissions.Condition (zero location index) next (protections.contains node.tag)) :
    Profile tree (updated tree location index node protections recorded next delta) protections := by
  intro query queryNode inArea found
  rw [zero_frame location _ frame query]
  by_cases same : query = index
  · subst query
    have sameNode := Option.some.inj (present.symm.trans found)
    subst queryNode
    simpa only [effective,updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some] using good
  · simpa only [effective,updated_other tree location index query node protections recorded next delta same] using initial query queryNode inArea found

theorem local_nonzero (initial : LocationTree) (root index : UniIndex)
    (positive : 0 < GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache root .Write)
    (related : related initial root index = .LocalAccess) :
    GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write ≠ 0 := by
  unfold GeneralBorrowExposedKnownRootWriteState.related at related
  split at related
  · have eq : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache root .Write = GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write := Nat.eq_of_beq_eq_true ‹_ = true›
    omega
  · split at related <;> cases related
theorem primary_classify (initial current : LocationTree) (root index : UniIndex)
    (frame : WriteFrame initial current) (positive : 0 < GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache root .Write) :
    current.exposedCache.accessRelatedness root index .Write false false = some (related initial root index) := by
  have counts : ∀ query, GeneralBorrowWildcardRelatednessBounds.count current.exposedCache query .Write = GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache query .Write :=
    fun query => congrArg UInt16.toNat (frame query)
  have rootPositive : GeneralBorrowWildcardRelatednessBounds.count current.exposedCache root .Write ≠ 0 := by rw [counts];omega
  simp only [ExposedCache.accessRelatedness,Id.run,pure,Bool.false_eq_true,ite_false,Nat.add_zero]
  change (if GeneralBorrowWildcardRelatednessBounds.count current.exposedCache root .Write == 0 then none else
    if GeneralBorrowWildcardRelatednessBounds.count current.exposedCache root .Write == GeneralBorrowWildcardRelatednessBounds.count current.exposedCache index .Write then some WildcardAccessRelatedness.LocalAccess else
    if GeneralBorrowWildcardRelatednessBounds.count current.exposedCache index .Write == 0 then some WildcardAccessRelatedness.ForeignAccess else some WildcardAccessRelatedness.EitherAccess) = _
  simp only [counts,show (GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache root .Write == 0) = false by simp [Nat.ne_of_gt positive],Bool.false_eq_true,ite_false,related]
  split <;> first | rfl | (split <;> rfl)

theorem positive_not_foreign (initial : LocationTree) (root index : UniIndex)
    (positive : 0 < GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write) :
    related initial root index ≠ .ForeignAccess := by
  unfold related
  split
  · decide
  · simp only [show (GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write == 0) = false by simp [Nat.ne_of_gt positive],Bool.false_eq_true,ite_false]
    decide
theorem foreign_zero (initial : LocationTree) (root index : UniIndex)
    (foreign : related initial root index = .ForeignAccess) : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write = 0 := by
  unfold related at foreign
  split at foreign
  · cases foreign
  · split at foreign
    · simpa only [beq_iff_eq] using ‹(GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Write == 0) = true›
    · cases foreign

end DuplicatePrefix.GeneralBorrowExposedKnownRootWriteState
