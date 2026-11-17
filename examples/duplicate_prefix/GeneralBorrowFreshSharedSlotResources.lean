import duplicate_prefix.GeneralBorrowForestSharedData
import duplicate_prefix.GeneralBorrowFreshSharedGeometry

namespace DuplicatePrefix.GeneralBorrowFreshSharedSlotResources
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Real shared construction preserves arbitrary coherent allocator pools and
partition geometry; its sparse node capacity grows by at most one. These are
actual poststate facts, not a successful-allocator premise. -/
theorem preserves (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.indexOfTag parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (allocator : GeneralBorrowGcAllocator.Invariant tree) :
    let after := GeneralBorrowFreshMetadataChildSlot.result tree parentTag newTag isProtected offset len
    GeneralBorrowGcAllocator.Invariant after ∧ after.locations.WellFormed ∧
      after.locations.size = tree.locations.size ∧ after.nodes.size ≤ tree.nodes.size+1 := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,isProtected,offset,len,nonzero,well,bounds⟩
    have geometry := GeneralBorrowFreshSharedGeometry.append_frame input
    have size := (GeneralBorrowFreshMetadataChildShared.append input).size
    exact ⟨GeneralBorrowSharedAllocatorInvariant.Append.preserves input allocator,geometry.1,geometry.2,Nat.le_of_eq size⟩
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        index,available,bounded,vacant,slack,isProtected,offset,len,nonzero,well,bounds⟩
    have geometry := GeneralBorrowFreshSharedGeometry.reuse_frame input
    have size := (GeneralBorrowFreshMetadataChildSharedReuse.reuse input).size
    refine ⟨GeneralBorrowSharedAllocatorInvariant.Reuse.preserves input allocator,geometry.1,geometry.2,?_⟩
    have sameSize : (GeneralBorrowFreshMetadataChildSlot.result tree parentTag newTag isProtected offset len).nodes.size = tree.nodes.size := size
    rw [sameSize]
    exact Nat.le_succ _

/-- Finite initial headroom forms the NEXT constructor's real general-root
Resources. No roots singleton, empty-free-pool or operation-success assumption
is added. One unit of the explicit node budget is consumed. -/
def next (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.indexOfTag parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree depth parent)
    (isProtected : Bool) (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (allocator : GeneralBorrowGcAllocator.Invariant tree) (room : tree.nodes.size+5 ≤ 4294967295) :
    GeneralBorrowForestSharedData.Resources
      (GeneralBorrowFreshMetadataChildSlot.result tree parentTag newTag isProtected offset len) := by
  let metadata := GeneralBorrowFreshMetadataChildSlot.build tree depth children covered parentTag newTag parent parentNode
    parentTagPresent parentPresent fresh slot isProtected offset len nonzero well bounds
  have facts := preserves tree depth children covered parentTag newTag parent parentNode parentTagPresent parentPresent fresh slot
    isProtected offset len nonzero well bounds allocator
  exact {
    depth := metadata.certificates.depth
    children := metadata.certificates.children
    allocator := facts.1
    well := facts.2.1
    room := by have size := facts.2.2.2;omega }

end DuplicatePrefix.GeneralBorrowFreshSharedSlotResources
