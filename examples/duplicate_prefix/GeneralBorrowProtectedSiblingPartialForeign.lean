import duplicate_prefix.GeneralBorrowProtectedReadInvariantLocation
import duplicate_prefix.GeneralBorrowProtectedSiblingForeignReadQuiet
import duplicate_prefix.GeneralBorrowProtectedReadPermissionMetadata
import duplicate_prefix.GeneralBorrowProtectedReadSingleRoot
import duplicate_prefix.GeneralBorrowTerminal
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutable
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingPartialForeign
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowExposure BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem foreign (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags) (location : LocationTree)
    (roots : input.tree.roots = #[input.parent])
    (query : UniIndex) (node : TreeNode) (present : input.tree.nodeAt query = some node) (parent : node.parent = some input.parent)
    (forest : GeneralBorrowForest.Forest (source_normal_projection input.tree location protections).topology) :
    ∀ event ∈ ((source_normal_projection input.tree location protections).topology.traverse input.parent.toNat .VisitChildrenOfAccessed
      (sourceNormalSkipped (source_normal_projection input.tree location protections) .Read)).2,
      event.node = query.toNat → event.relatedness = .ForeignAccess := by
  let normal := source_normal_projection input.tree location protections
  have valid := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor input.tree location protections input.parent input.parentNode input.parentPresent
  have lastRoot := GeneralBorrowTerminal.ancestor_root_present normal.topology forest (GeneralBorrowGraph.Present input.tree)
    (GeneralBorrowGraph.parents_closed input.tree location protections input.depth) input.parent.toNat input.parent.toNat valid
    ⟨input.parent,input.parentNode,rfl,input.parentPresent⟩
    (fun index _ found parentless => GeneralBorrowGraph.unique_root input.tree location protections input.parent roots input.covered index found parentless)
  have terminal := GeneralBorrowTerminal.ancestor_terminal normal.topology forest input.parent.toNat valid
  rw [lastRoot] at terminal
  have path : normal.topology.ancestorPath input.parent.toNat = [input.parent.toNat] := by
    change sourceAncestorPath normal.topology normal.topology.nodes.size input.parent.toNat = _
    cases normal.topology.nodes.size with
    | zero => rfl
    | succ fuel => rw [GeneralBorrowPresence.ancestor_succ,terminal]
  have different : query.toNat ≠ input.parent.toNat := by
    intro equal
    have same := GeneralBorrowNodeUpdate.index_injective query input.parent equal
    obtain ⟨earlier,found,less⟩ := input.depth.parent query node present input.parent parent
    rw [same] at less
    omega
  intro event member equal
  have schedule := GeneralBorrowTraversal.traversal_data normal.topology forest input.parent.toNat valid .VisitChildrenOfAccessed (sourceNormalSkipped normal .Read)
  rw [(schedule.2 event member).2,equal,path]
  simp only [List.mem_singleton,different,↓reduceIte]

theorem location (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags) (location : LocationTree) (range : ByteRange)
    (roots : input.tree.roots = #[input.parent])
    (query : UniIndex) (node : TreeNode) (present : input.tree.nodeAt query = some node) (parent : node.parent = some input.parent)
    (forest : GeneralBorrowForest.Forest (source_normal_projection input.tree location protections).topology)
    (readable : GeneralBorrowProtectedReadInvariantLocation.Data input.tree protections location)
    (quiet : GeneralBorrowProtectedSiblingForeignReadQuiet.LocationTyped location query) :
    GeneralBorrowProtectedSiblingForeignReadQuiet.LocationTyped
      (source_access_location (source_tree_access_at input.tree location (some input.parent) .Read protections .VisitChildrenOfAccessed range)) query := by
  have valid := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor input.tree location protections input.parent input.parentNode input.parentPresent
  have compatible := GeneralBorrowProtectedReadPermissionMetadata.compatible_initial input.tree location protections input.parent readable
  rw [GeneralBorrowProtectedReadSingleRoot.single_root_location input.tree location protections input.parent input.parent .VisitChildrenOfAccessed range
    forest valid compatible input.depth input.children input.parentNode input.parentPresent roots input.covered]
  exact GeneralBorrowProtectedSiblingForeignReadQuiet.normal input.tree location protections input.parent query .VisitChildrenOfAccessed quiet
    (foreign input protections location roots query node present parent forest)
end DuplicatePrefix.GeneralBorrowProtectedSiblingPartialForeign
