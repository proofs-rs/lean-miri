import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultOld
import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant
import duplicate_prefix.GeneralBorrowFreshFutureClean
import duplicate_prefix.GeneralBorrowGcVacantClean
namespace DuplicatePrefix.GeneralBorrowExposedScopedDefaultConstructorAllocator
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildDefault
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem nodeTags (input : Input) (initial : GeneralBorrowGcAllocator.NodeTags input.tree) :
    GeneralBorrowGcAllocator.NodeTags (result input) := by
  have staged := GeneralBorrowSharedAllocatorInvariant.staged_tags input.tree (index input) input.parent input.parentNode
    (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) input.newTag rfl input.tree.tagMapping.deassigned
    (locations input) input.parentPresent input.fresh initial
  have coherent : GeneralBorrowGcAllocator.NodeTags (stage input) := by simpa only [stage,mapping] using staged
  exact GeneralBorrowSharedAllocatorInvariant.shape_tags (stage input) (result input) (shape input) coherent

theorem clean (input : Input) (initial : GeneralBorrowGcVacantClean.VacantClean input.tree) :
    GeneralBorrowGcVacantClean.VacantClean (result input) := by
  let metadata := GeneralBorrowFreshMetadataChildDefault.append input
  intro query vacant
  have different : query≠index input := by
    intro same
    obtain ⟨node,present,_,_,_,_,_⟩ := metadata.newNode
    rw [same] at vacant
    change (result input).nodeAt (index input)=none at vacant
    rw [present] at vacant
    cases vacant
  have originalVacant : input.tree.nodes.get query=none := by
    cases previous : input.tree.nodes.get query with
    | none => rfl
    | some node =>
      obtain ⟨next,present,_,_⟩ := GeneralBorrowFreshMetadataChildDefaultOld.append input query node previous
      change (result input).nodeAt query=none at vacant
      rw [vacant] at present
      cases present
  have modified := GeneralBorrowFreshFutureClean.modified input.tree.locations (index input) query
    (Size.ofBytes input.offset) (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside different
    input.well input.bounds (initial query originalVacant)
  have stageClean : GeneralBorrowFreshFutureClean.Clean (stage input) query := modified
  exact GeneralBorrowFreshFutureClean.shape_preserves _ _ (shape input) query stageClean
end DuplicatePrefix.GeneralBorrowExposedScopedDefaultConstructorAllocator
