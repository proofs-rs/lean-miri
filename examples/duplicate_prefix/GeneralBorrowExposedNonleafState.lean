import duplicate_prefix.GeneralBorrowExposedNonleafRead
import duplicate_prefix.GeneralBorrowWildcardSubtreeInvariant
import duplicate_prefix.GeneralBorrowExposedVirtualSchedule

namespace DuplicatePrefix.GeneralBorrowExposedNonleafState
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective materialized onlyForeign)
open GeneralBorrowWildcardSubtreeState (write write_same write_other)
open GeneralBorrowExposureCardinality (counter)
set_option maxRecDepth 65536
set_option maxHeartbeats 200000

def Readable (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) : Prop :=
  ∀ index node, tree.nodes.get index = some node →
    GeneralBorrowProtectedReadInvariant.Readable (effective location index node) (protections.contains node.tag)

def ReadFrame (before after : LocationTree) : Prop :=
  ∀ query, counter after.exposedCache query .Read = counter before.exposedCache query .Read

def foreign (initial : LocationTree) (index : UniIndex) (node : TreeNode) (maximum : Option Miri.Memory.BorTag) : Bool :=
  onlyForeign node maximum || GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index .Read == 0

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

def updated (tree : BorrowTree) (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (protections : ProtectedTags) (recorded next : LocationState) (delta : PermTransition) : LocationTree :=
  {write location index node recorded next with exposedCache :=
    if node.isExposed && !delta.isNoop then
      (location.exposedCache.updateExposure tree.nodes index
        ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag))
        (next.permission.strongestAllowedLocalAccess (protections.contains node.tag))).cache
    else location.exposedCache}

theorem updated_other (tree : BorrowTree) (location : LocationTree) (index query : UniIndex) (node : TreeNode)
    (protections : ProtectedTags) (recorded next : LocationState) (delta : PermTransition) (different : query ≠ index) :
    (updated tree location index node protections recorded next delta).perms.get query = location.perms.get query := by
  dsimp only [updated]
  exact write_other location index query node recorded next different

theorem updated_readable (tree : BorrowTree) (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (protections : ProtectedTags) (recorded next : LocationState) (delta : PermTransition)
    (present : tree.nodes.get index = some node) (initial : Readable tree location protections)
    (good : GeneralBorrowProtectedReadInvariant.Readable next (protections.contains node.tag)) :
    Readable tree (updated tree location index node protections recorded next delta) protections := by
  intro query queryNode found
  by_cases same : query = index
  · subst query
    have sameNode := Option.some.inj (present.symm.trans found)
    subst queryNode
    simpa only [effective,updated,write_same,Option.getD_some] using good
  · simpa only [effective,updated_other tree location index query node protections recorded next delta same] using initial query queryNode found

theorem updated_frame (tree : BorrowTree) (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (protections : ProtectedTags) (recorded next : LocationState) (delta : PermTransition)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (present : tree.nodes.get index = some node)
    (support : GeneralBorrowExposureCardinality.supports
      (next.permission.strongestAllowedLocalAccess (protections.contains node.tag)) .Read =
      GeneralBorrowExposureCardinality.supports
        ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)) .Read) :
    ReadFrame location (updated tree location index node protections recorded next delta) := by
  intro query
  unfold updated
  dsimp only
  split
  · rw [GeneralBorrowExposurePointwise.update_counter _ _ depth index node present]
    rw [support]
    cases GeneralBorrowExposureCardinality.supports
      ((effective location index node).permission.strongestAllowedLocalAccess (protections.contains node.tag)) .Read <;>
      simp [GeneralBorrowExposureAncestorFold.delta]
  · rfl

theorem materialized_readable (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (node : TreeNode)
    (protections : ProtectedTags) (present : tree.nodes.get root = some node) (initial : Readable tree location protections) :
    Readable tree (materialized location root node) protections := by
  intro query queryNode found
  rw [GeneralBorrowExposedVirtualSchedule.materialized_effective tree location root node present query queryNode found]
  exact initial query queryNode found

end DuplicatePrefix.GeneralBorrowExposedNonleafState
