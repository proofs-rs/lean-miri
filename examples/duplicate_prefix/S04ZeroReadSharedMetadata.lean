import duplicate_prefix.S04ZeroReadSharedCallbacks
import duplicate_prefix.GeneralRangeMapState

namespace DuplicatePrefix.S04ZeroReadSharedMetadata
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifa GeneralBorrowView GeneralBorrowFreshGraph GeneralBorrowNodeUpdate
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

theorem roots (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadSharedEntry.Input tree parentTag tag) : input.after.roots = tree.roots :=
  GeneralBorrowFreshMetadata.roots input.stage input.after (GeneralBorrowSifaView.preserves input.stage input.parent .Read)

theorem ranges (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadSharedEntry.Input tree parentTag tag) :
    input.after.locations.entries.map (·.range) = tree.locations.entries.map (·.range) := by
  have shape := congrArg (fun value => value.2.2.1) (GeneralBorrowSifaView.preserves input.stage input.parent .Read)
  change input.after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) =
    tree.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at shape
  have mapped := congrArg (Array.map Prod.fst) shape
  simpa only [Array.map_map,Function.comp_def] using mapped

theorem length (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadSharedEntry.Input tree parentTag tag) :
    input.after.locations.entries.size = tree.locations.entries.size := by
  have same := congrArg Array.size (ranges tree parentTag tag input)
  simpa only [Array.size_map] using same

theorem capacity (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadSharedEntry.Input tree parentTag tag) : input.after.locations.size = tree.locations.size := by
  rw [GeneralRangeMapState.size_from_ranges,ranges tree parentTag tag input,←GeneralRangeMapState.size_from_ranges]

theorem row_range (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadSharedEntry.Input tree parentTag tag) (position : Nat)
    (oldValid : position < tree.locations.entries.size) (newValid : position < input.after.locations.entries.size) :
    (input.after.locations.entries[position]'newValid).range = (tree.locations.entries[position]'oldValid).range := by
  have same := congrArg (fun rows => rows[position]?) (ranges tree parentTag tag input)
  simpa only [Array.getElem?_map,Array.getElem?_eq_getElem oldValid,Array.getElem?_eq_getElem newValid,
    Option.map_some,Option.some.injEq] using same

/-- Every old node stays present with the same tag through both real allocator
branches and the exact ancestor-SIFA result. No spatial/component separation
from the constructor parent is needed. -/
theorem old_node (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadSharedEntry.Input tree parentTag tag)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node) :
    ∃ next,input.after.nodeAt query = some next ∧ next.tag = node.tag := by
  let staged := S04ZeroReadSharedAttach.liftNode input.parent input.index query node
  have stagePresent : input.stage.nodeAt query = some staged :=
    S04ZeroReadSharedAttach.old_lookup tree input.index input.parent input.parentNode
      (GeneralBorrowFreshAnchor.sharedNode tag input.parent) input.vacant input.present query node present
  obtain ⟨next,found,tagEq,parent,children,permission,exposed⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
    input.stage input.parent .Read query staged stagePresent
  refine ⟨next,found,?_⟩
  have tagSame : staged.tag = node.tag := by
    by_cases same : query = input.parent <;> simp only [staged,S04ZeroReadSharedAttach.liftNode,same,ite_true,ite_false]
  exact tagEq.trans tagSame

end DuplicatePrefix.S04ZeroReadSharedMetadata
