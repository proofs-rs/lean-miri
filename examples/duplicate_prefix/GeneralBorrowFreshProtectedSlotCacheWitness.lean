import duplicate_prefix.GeneralBorrowFreshCacheWitness
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableSlot

namespace DuplicatePrefix.GeneralBorrowFreshProtectedSlotCacheWitness
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReborrowStages (Slot)
open GeneralBorrowFreshCacheWitness (Witness)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The REAL protected Default constructor preserves a same-origin cache/data witness on
its full selected slice, through range preparation, inside materialization and
ancestor SIFA. Both allocator branches are handled without successful-operation
premises; the arbitrary predicate can carry the preceding Read's next records. -/
theorem owned (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.indexOfTag parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (predicate : LocationTree → Prop)
    (before : GeneralRangeMapOrigins.OwnedOn predicate offset (offset+len) tree.locations) :
    GeneralRangeMapOrigins.OwnedOn (Witness predicate) offset (offset+len)
      (GeneralBorrowFreshMetadataChildMutableSlot.result tree parentTag newTag offset len).locations := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
    have modified := GeneralBorrowFreshCacheWitness.modified tree.locations (Size.ofBytes offset) (Size.ofBytes len)
      (fun _ location => GeneralBorrowFreshMaterialization.materialized location (GeneralBorrowFreshMetadataChildMutable.index input) GeneralBorrowFreshChild.inside)
      (fun _ location => GeneralBorrowFreshInstallation.materialized_idempotent location _ _)
      (fun _ _ => rfl) well bounds predicate offset (offset+len) before (Nat.le_refl _) (Nat.le_refl _)
    have stageWitness : GeneralRangeMapOrigins.OwnedOn (Witness predicate) offset (offset+len)
        (GeneralBorrowFreshMetadataChildMutable.stage input).locations := modified
    have shape : GeneralBorrowSifaCacheFrame.cacheShape (GeneralBorrowFreshMetadataChildMutable.result input) =
        GeneralBorrowSifaCacheFrame.cacheShape (GeneralBorrowFreshMetadataChildMutable.stage input) := by
      rw [GeneralBorrowFreshMetadataChildMutable.tree_eq]
      exact GeneralBorrowSifaCacheFrame.sifa_cache _ parent .None
    exact GeneralBorrowFreshCacheWitness.shape_preserves _ _ shape predicate offset (offset+len) stageWitness
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,well,bounds⟩
    have modified := GeneralBorrowFreshCacheWitness.modified tree.locations (Size.ofBytes offset) (Size.ofBytes len)
      (fun _ location => GeneralBorrowFreshMaterialization.materialized location index GeneralBorrowFreshChild.inside)
      (fun _ location => GeneralBorrowFreshInstallation.materialized_idempotent location _ _)
      (fun _ _ => rfl) well bounds predicate offset (offset+len) before (Nat.le_refl _) (Nat.le_refl _)
    have stageWitness : GeneralRangeMapOrigins.OwnedOn (Witness predicate) offset (offset+len)
        (GeneralBorrowFreshMetadataChildMutableReuse.stage input).locations := by
      simpa only [GeneralBorrowFreshMetadataChildMutableReuse.stage,GeneralBorrowFreshMetadataChildAttach.staged,
        GeneralBorrowFreshMetadataChildMutableReuse.locations,GeneralBorrowFreshMetadataChildMutableReuse.index,input] using modified
    have shape : GeneralBorrowSifaCacheFrame.cacheShape (GeneralBorrowFreshMetadataChildMutableReuse.result input) =
        GeneralBorrowSifaCacheFrame.cacheShape (GeneralBorrowFreshMetadataChildMutableReuse.stage input) := by
      rw [GeneralBorrowFreshMetadataChildMutableReuse.tree_eq]
      exact GeneralBorrowSifaCacheFrame.sifa_cache _ parent .None
    exact GeneralBorrowFreshCacheWitness.shape_preserves _ _ shape predicate offset (offset+len) stageWitness

end DuplicatePrefix.GeneralBorrowFreshProtectedSlotCacheWitness
