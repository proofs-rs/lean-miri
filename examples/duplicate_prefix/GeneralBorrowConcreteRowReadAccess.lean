import duplicate_prefix.GeneralBorrowConcreteRowAccess
namespace DuplicatePrefix.GeneralBorrowConcreteRowReadAccess
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
set_option autoImplicit false
abbrev State := GeneralBorrowConcreteRowAccess.State

def scan (tree : BorrowTree) (selected : UniIndex) (maximum minimum : Option BorTag)
    (protections : ProtectedTags) (mode : ChildrenVisitMode) (range : ByteRange)
    (position : Nat) (state : State) : Id (ForInStep State) :=
  GeneralBorrowConcreteRowAccess.scan tree selected maximum minimum .Read protections mode range position state

abbrev Good (tree : BorrowTree) (protections : ProtectedTags) (anchor selected : UniIndex)
    (maximum : Option BorTag) (state : State) : Prop :=
  GeneralBorrowConcreteRowAccess.Good tree protections anchor selected maximum state

theorem roots (tree : BorrowTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum minimum : Option BorTag) (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange)
    (initial : State) (good : Good tree protections anchor selected maximum initial) :
    Good tree protections anchor selected maximum
      (forIn (List.range' 0 tree.roots.size) initial (scan tree selected maximum minimum protections mode range) : Id State) := by
  exact GeneralBorrowConcreteRowAccess.roots tree protections formed anchor selected anchorNode present maximum minimum .Read
    distinct order short mode range initial good

theorem access_when_primary (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : Option BorTag)
    (row : DuplicatePrefixBorrowAuthorization.Row tree location protections (some anchor) (some selected) maximum)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree location (some anchor) .Read protections mode range
    source_access_status result = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (source_access_location result) protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Row tree (source_access_location result) protections (some anchor) (some selected) maximum) := by
  exact GeneralBorrowConcreteRowAccess.access_when_primary tree location protections formed anchor selected anchorNode present maximum .Read row
    distinct order coherent profile possible short mode range

theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : Option BorTag)
    (row : DuplicatePrefixBorrowAuthorization.Row tree location protections (some anchor) (some selected) maximum)
    (distinct : tree.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree location (some anchor) .Read protections mode range
    source_access_status result = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (source_access_location result) protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Row tree (source_access_location result) protections (some anchor) (some selected) maximum) := by
  exact GeneralBorrowConcreteRowAccess.access tree location protections formed anchor selected anchorNode present maximum .Read row
    distinct order coherent profile possible short mode range
end DuplicatePrefix.GeneralBorrowConcreteRowReadAccess
