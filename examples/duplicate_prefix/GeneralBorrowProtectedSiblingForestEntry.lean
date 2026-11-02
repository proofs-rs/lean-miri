import duplicate_prefix.GeneralBorrowProtectedSiblingFunctionNumerics
import duplicate_prefix.GeneralBorrowCanonicalParentDepth
import duplicate_prefix.GeneralBorrowFreshSharedWithinStages
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingForestEntry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralBorrowRange GeneralBorrowProjection GeneralBorrowProtectedSiblingGenerationBounds
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Embed a singleton covered forest's root ownership into the general
multiple-root FnEntry contract. The extra-root region is the empty region. -/
def build (tree : BorrowTree) (protections : ProtectedTags) (root : UniIndex) (rootNode : TreeNode)
    (parentTag newTag : BorTag) (len : UInt64)
    (present : tree.nodeAt root = some rootNode) (tagPresent : tree.indexOfTag parentTag = some root)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (covered : GeneralBorrowGraph.RootsCover tree) (roots : tree.roots = #[root])
    (hidden : ∀ index node,tree.nodeAt index = some node → node.isExposed = false)
    (allocator : GeneralBorrowGcAllocator.Invariant tree) (room : tree.nodes.size+8 ≤ 4294967295)
    (well : tree.locations.WellFormed) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (unheld : protections.get newTag = none)
    (owned : Every (GeneralBorrowRange.LocationOwned tree protections root .Write) tree.locations) :
    GeneralBorrowForestEntryValidity.Data tree protections parentTag newTag 0 len := by
  have room' : tree.nodes.data.size+8 ≤ 4294967295 := room
  let context : GeneralBorrowForestAccessData.Context tree root root [] := {
    anchorNode := rootNode,primaryNode := rootNode,depth := GeneralBorrowCanonicalParentDepth.normalize tree.nodes depth,
    children := children,anchorPresent := present,primaryPresent := present,roots := roots,different := by simp,
    unexposed := hidden }
  let slot := GeneralBorrowCanonicalParentDepth.slot tree depth root rootNode present allocator.pool
    (GeneralBorrowFreshStagePool.empty_aligned tree allocator.accounting)
    (by intro empty;have aligned := GeneralBorrowFreshStagePool.empty_aligned tree allocator.accounting empty;omega)
  refine {
    parent := root,primary := root,extras := [],context := context,covered := covered,tagPresent := tagPresent,
    tagFresh := fresh,globalUnheld := unheld,nodeTags := allocator.nodeTags,nodeFits := (by omega),
    slot := slot,well := well,owned := ?_}
  intro position valid _ _ _
  obtain ⟨⟨forest⟩,owner⟩ := owned position valid
  let location := tree.locations.entries[position].data
  have anchorValid := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree location protections root rootNode present
  have lastRoot := GeneralBorrowTerminal.ancestor_root_present (source_normal_projection tree location protections).topology forest
    (GeneralBorrowGraph.Present tree) (GeneralBorrowGraph.parents_closed tree location protections depth) root.toNat root.toNat anchorValid
    ⟨root,rootNode,rfl,present⟩
    (fun index _ found parentless => GeneralBorrowGraph.unique_root tree location protections root roots covered index found parentless)
  exact ⟨{
    base := {
      forest := forest
      owned := owner
      rootPath := lastRoot
      region := {
        support := fun _ => False
        present := by simp
        children := by simp
        unexposed := by simp
        zero := by simp
        owned := by simp }
      supported := by simp
      foreignGraph := by simp }
    readZero := by simp }⟩


theorem clean (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag) (offset len : UInt64)
    (data : GeneralBorrowForestEntryValidity.Data tree protections parentTag newTag offset len)
    (vacant : GeneralBorrowGcVacantClean.VacantClean tree) :
    Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutableSlot.index data.slot) = none) tree.locations := by
  apply vacant
  exact GeneralBorrowFreshSharedWithinStages.slot_vacant tree data.context.depth data.parent data.slot
end
end DuplicatePrefix.GeneralBorrowProtectedSiblingForestEntry
