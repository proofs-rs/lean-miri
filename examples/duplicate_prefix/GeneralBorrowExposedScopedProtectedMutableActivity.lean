import duplicate_prefix.GeneralBorrowFreshActiveWithinInsert
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutable
namespace DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableActivity
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshChild DuplicatePrefix.GeneralBorrowNodeUpdate
open DuplicatePrefix.GeneralBorrowFreshMaterialization
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
private theorem modified_sifa (tree : BorrowTree) (index parent : UniIndex) (offset len : Size)
    (well : tree.locations.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : ∀ position (valid : position < tree.locations.entries.size), tree.locations.entries[position].data.perms.get index = none) :
    GeneralBorrowFreshActiveWithin.ActiveWithin
      (sourceUpdateSifa {tree with locations := (tree.locations.modifyRange offset len (fun _ location => materialized location index inside)).state}
        parent .None).1 index .Read offset.bytes (offset.bytes+len.bytes) := by
  have active := GeneralBorrowFreshActiveWithinInsert.modified tree index offset len inside .Read (by intro kind associated _;cases associated;rfl) well bounds clean
  exact GeneralBorrowFreshActiveWithin.sifa_preserves
    {tree with locations := (tree.locations.modifyRange offset len (fun _ location => materialized location index inside)).state}
    parent .None index .Read offset.bytes (offset.bytes+len.bytes) active

theorem append (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (noFree : tree.tagMapping.deassigned.back? = none) (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ = none) :
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) inside) (.ReservedFrz false) true
    GeneralBorrowFreshActiveWithin.ActiveWithin result.tree index .Read offset (offset+len) := by
  dsimp only
  rw [GeneralBorrowFreshResult.mutable_tree tree parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh noFree aligned fits offset len nonzero well bounds]
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  let base : BorrowTree := {(GeneralBorrowFreshGraph.attached tree index parent parentNode (child newTag parent)) with
    tagMapping := ⟨tree.tagMapping.mapping.push (newTag,index),tree.tagMapping.deassigned⟩}
  have wellBase : base.locations.WellFormed := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact well
  have boundsBase : offset.toNat+len.toNat ≤ base.locations.size.bytes.toNat := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact bounds
  have cleanBase : ∀ position (valid : position < base.locations.entries.size), base.locations.entries[position].data.perms.get index = none := by
    dsimp only [base,GeneralBorrowFreshGraph.attached]
    exact clean
  have active := modified_sifa base index parent (Size.ofBytes offset) (Size.ofBytes len) wellBase boundsBase cleanBase
  simpa only [base,index,materialized,GeneralBorrowFreshGraph.attached,Size.ofBytes] using active

end DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableActivity
