import duplicate_prefix.GeneralBorrowExposedConditionalReadPermissions
import duplicate_prefix.GeneralBorrowWildcardSubtreeInvariant
import duplicate_prefix.GeneralBorrowExposedVirtualSchedule

namespace DuplicatePrefix.GeneralBorrowExposedKnownRootState
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective materialized onlyForeign)
open GeneralBorrowWildcardSubtreeState (write write_same write_other)
open GeneralBorrowExposureCardinality (counter)
set_option maxRecDepth 65536
set_option maxHeartbeats 200000

/-- Pure common scope for the nonselected physical components. -/
class Scope where
  support : UniIndex → Prop
variable [area : Scope]

def zero (location : LocationTree) (index : UniIndex) : Bool :=
  GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Read == 0

def Readable (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) : Prop :=
  ∀ index node, area.support index → tree.nodes.get index = some node →
    GeneralBorrowExposedConditionalReadPermissions.Condition (zero location index) (effective location index node) (protections.contains node.tag)

open GeneralBorrowExposedNonleafState (ReadFrame foreign updated updated_other updated_frame)

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
  readable : Readable tree initial protections

theorem classify {tree initial root protections} (data : Data tree initial root protections)
    (location : LocationTree) (frame : ReadFrame initial location) (index : UniIndex) (node : TreeNode)
    (supported : data.support index) (maximum : Option Miri.Memory.BorTag) :
    location.exposedCache.accessRelatedness root index .Read true (onlyForeign node maximum) =
      some (if foreign initial index node maximum then .ForeignAccess else .EitherAccess) := by
  have countEq : ∀ query, GeneralBorrowWildcardRelatednessBounds.count location.exposedCache query .Read =
      GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache query .Read :=
    fun query => congrArg UInt16.toNat (frame query)
  have bounded := GeneralBorrowExposureCardinality.dominates initial.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective initial protections) data.coherent data.short root index (data.covers index supported) .Read
  change GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Read ≤ GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache root .Read at bounded
  rw [GeneralBorrowWildcardRelatednessBounds.virtual_classify _ _ _ _ _ (by simpa only [countEq] using bounded)]
  simp only [countEq,foreign]
  rfl


theorem zero_frame (before after : LocationTree) (frame : ReadFrame before after) (query : UniIndex) : zero after query = zero before query := by
  unfold zero
  have eq : GeneralBorrowWildcardRelatednessBounds.count after.exposedCache query .Read = GeneralBorrowWildcardRelatednessBounds.count before.exposedCache query .Read := congrArg UInt16.toNat (frame query)
  rw [eq]

theorem foreign_compatible (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (frame : ReadFrame initial current) (profile : Readable tree current protections)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (inArea : area.support index)
    (isZero : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Read = 0) :
    GeneralBorrowProtectedReadCompatible.Compatible (effective current index node) .ForeignAccess (protections.contains node.tag) := by
  have good := profile index node inArea present
  have eq : zero current index = true := by rw [zero_frame initial current frame index];simp [zero,isZero]
  simpa only [GeneralBorrowExposedConditionalReadPermissions.Condition,eq,ite_true] using good

theorem local_compatible (tree : BorrowTree) (initial current : LocationTree) (protections : ProtectedTags)
    (frame : ReadFrame initial current) (profile : Readable tree current protections)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (inArea : area.support index)
    (nonzero : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Read ≠ 0) :
    GeneralBorrowProtectedReadCompatible.Compatible (effective current index node) .LocalAccess (protections.contains node.tag) := by
  have good := profile index node inArea present
  have eq : zero current index = false := by rw [zero_frame initial current frame index];simp [zero,nonzero]
  simpa only [GeneralBorrowExposedConditionalReadPermissions.Condition,eq,Bool.false_eq_true,ite_false] using good

theorem materialized_readable (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (node : TreeNode)
    (protections : ProtectedTags) (present : tree.nodes.get root = some node) (initial : Readable tree location protections) :
    Readable tree (materialized location root node) protections := by
  intro query queryNode inArea found
  rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree location root node present query queryNode found]
  exact initial query queryNode inArea found

theorem updated_readable (tree : BorrowTree) (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (protections : ProtectedTags) (recorded next : LocationState) (delta : PermTransition)
    (present : tree.nodes.get index = some node) (initial : Readable tree location protections)
    (frame : ReadFrame location (updated tree location index node protections recorded next delta))
    (good : GeneralBorrowExposedConditionalReadPermissions.Condition (zero location index) next (protections.contains node.tag)) :
    Readable tree (updated tree location index node protections recorded next delta) protections := by
  intro query queryNode inArea found
  rw [zero_frame location _ frame query]
  by_cases same : query = index
  · subst query
    have sameNode := Option.some.inj (present.symm.trans found)
    subst queryNode
    simpa only [effective,updated,GeneralBorrowWildcardSubtreeState.write_same,Option.getD_some] using good
  · simpa only [effective,updated_other tree location index query node protections recorded next delta same] using initial query queryNode inArea found

theorem local_nonzero (initial : LocationTree) (root index : UniIndex)
    (positive : 0 < GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache root .Read)
    (related : GeneralBorrowExposedNonleafPrimaryState.related initial root index = .LocalAccess) :
    GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Read ≠ 0 := by
  unfold GeneralBorrowExposedNonleafPrimaryState.related at related
  split at related
  · have eq : GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache root .Read = GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Read := Nat.eq_of_beq_eq_true ‹_ = true›
    omega
  · split at related <;> cases related
end DuplicatePrefix.GeneralBorrowExposedKnownRootState
