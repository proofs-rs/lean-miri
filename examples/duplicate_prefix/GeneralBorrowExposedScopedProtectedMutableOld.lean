import duplicate_prefix.GeneralBorrowFreshMetadataChildMutable
import duplicate_prefix.GeneralBorrowExposureSifaTransport
import duplicate_prefix.GeneralBorrowExposureChildAttach
import duplicate_prefix.GeneralBorrowSifaUniqueFrame
namespace DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableOld
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildMutable
open GeneralBorrowView GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual concrete shared append preserves every old nonparent node's graph,
tag, default permission and exposure, including the real ancestor SIFA loop. -/
theorem outside_parent (input : Input) (query : UniIndex) (node : TreeNode)
    (present : input.tree.nodeAt query = some node) (different : query ≠ input.parent) :
    ∃ next, (result input).nodeAt query = some next ∧ next.tag = node.tag ∧
      next.parent = node.parent ∧ next.children = node.children ∧
      next.defaultInitialPermission = node.defaultInitialPermission ∧ next.isExposed = node.isExposed := by
  have notNew : query ≠ index input := by
    intro same
    have bound := lookup_valid input.tree.nodes query node present
    rw [same,at_end input] at bound
    omega
  have old := GeneralBorrowFreshGraph.other_lookup input.tree (index input) input.parent query input.parentNode
    (GeneralBorrowFreshChild.child input.newTag input.parent) (at_end input) input.parentPresent different notNew
  have staged : (stage input).nodeAt query = some node := by
    change (GeneralBorrowFreshGraph.attached input.tree (index input) input.parent input.parentNode
      (GeneralBorrowFreshChild.child input.newTag input.parent)).nodeAt query = _
    exact old.trans present
  obtain ⟨next,found,tag,parent,children,permission⟩ := GeneralBorrowFreshMetadata.node_fields
    (stage input) (result input) (shape input) query node staged
  have exposed := GeneralBorrowFreshMetadataChildSifa.lookup_exposure (stage input) (result input) (exposure input) query
  change (stage input).nodes.get query = some node at staged
  rw [found,staged] at exposed
  exact ⟨next,found,tag,parent,children,permission,by simpa only [Option.map_some,Option.some.injEq] using exposed⟩
/-- Exact stored Unique witnesses survive actual positive-range installation
and every ancestor SIFA branch, without a post-constructor witness premise. -/
theorem unique (input : Input) (query : UniIndex) (node : TreeNode)
    (present : input.tree.nodeAt query = some node)
    (initial : GeneralBorrowSifaUniqueFrame.UniqueAt input.tree query) :
    GeneralBorrowSifaUniqueFrame.UniqueAt (result input) query := by
  have different : query ≠ index input := by
    intro same
    have bound := lookup_valid input.tree.nodes query node present
    rw [same,at_end input] at bound
    omega
  have modified := GeneralBorrowExposureChildAttach.modify_every
    (fun location : LocationTree => location.perms.get query = some GeneralBorrowWildcardLeaf.unique)
    input.tree.locations (Size.ofBytes input.offset) (Size.ofBytes input.len)
    (fun _ location => GeneralBorrowFreshMaterialization.materialized location (index input) GeneralBorrowFreshChild.inside)
    input.well input.bounds initial (by
      intro range location stored
      exact (GeneralBorrowFreshLocation.get_other _ (index input) query _ different).trans stored)
  have stageUnique : GeneralBorrowSifaUniqueFrame.UniqueAt (stage input) query := modified
  rw [tree_eq input]
  exact GeneralBorrowSifaUniqueFrame.sifa_unique (stage input) input.parent .None query stageUnique

end DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableOld
