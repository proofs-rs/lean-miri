import duplicate_prefix.GeneralBorrowProtectedReadStable
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseStable
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.BorrowRangeAccess
open DuplicatePrefix.GeneralBorrowProtectedVirtualReadCache (StablePermission)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Only the selected prior tags must have Read-stable exposed permissions.
The currently held upcoming final reservation may remain unconflicted/exposed. -/
def ForTags (tags : List BorTag) (tree : BorrowTree) (location : LocationTree) : Prop :=
  ∀ index node,tree.nodeAt index = some node → node.isExposed = true → node.tag ∈ tags →
    StablePermission ((location.perms.get index).getD node.defaultLocationState).permission

theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (tags : List BorTag)
    (anchor : UniIndex) (mode : ChildrenVisitMode) (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (initial : GeneralBorrowProtectedReadInvariant.Data (source_normal_projection tree location protections))
    (stable : ForTags tags tree location) :
    ForTags tags tree (tree.performNormalAccessAt location anchor .Read protections mode).location := by
  intro query node present exposed member
  rw [GeneralBorrowProtectedReadStable.normal_permission tree location protections anchor mode depth children anchorNode anchorPresent forest initial
    query node present (stable query node present exposed member)]
  exact stable query node present exposed member

theorem virtual (tree : BorrowTree) (location : LocationTree) (actual pending : ProtectedTags) (tags : List BorTag)
    (coverage : ∀ tag,actual.contains tag ≠ pending.contains tag → tag ∈ tags) (stable : ForTags tags tree location) :
    GeneralBorrowProtectedVirtualReadCache.Stable tree location actual pending := by
  intro index node present exposed different
  exact ⟨(location.perms.get index).getD node.defaultLocationState,by simp [BorrowTree.locationStateAt,present],
    stable index node present exposed (coverage node.tag different)⟩

theorem location (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (tags : List BorTag)
    (anchor root : UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (initial : GeneralBorrowProtectedReadInvariant.Data (source_normal_projection tree location protections))
    (stable : ForTags tags tree location) :
    ForTags tags tree (source_access_location (source_tree_access_at tree location (some anchor) .Read protections mode range)) := by
  have valid := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree location protections anchor anchorNode anchorPresent
  have compatible := GeneralBorrowProtectedReadPermissionMetadata.compatible_initial tree location protections anchor initial
  rw [GeneralBorrowProtectedReadSingleRoot.single_root_location tree location protections anchor root mode range forest valid compatible
    depth children anchorNode anchorPresent roots covered]
  exact normal tree location protections tags anchor mode depth children anchorNode anchorPresent forest initial stable
end DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseStable
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseStable.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved sibling release stable dependency {dependency}"
