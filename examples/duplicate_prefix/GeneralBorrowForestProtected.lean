import duplicate_prefix.GeneralBorrowForestProtectedConstructor
import duplicate_prefix.GeneralBorrowForestMutableSlice
import duplicate_prefix.GeneralBorrowFreshReadFrame

namespace DuplicatePrefix.GeneralBorrowForestProtected
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestMutableAccess (Data)
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowFreshReborrowStages (Slot)
open GeneralBorrowFreshReadFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def read (tree : BorrowTree) (protections : ProtectedTags) (parentTag : BorTag)
    (offset len : UInt64) (mode : ChildrenVisitMode) :=
  tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections mode

def child (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (mode : ChildrenVisitMode) :=
  (read tree protections parentTag offset len mode).tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true

/-- The REAL ranged Read followed by the REAL protected Default mutable reservation (SIFA.None) completes
and forms every new-child next-input permission/cache/region/graph record.
Both visitor modes, arbitrary finite extra unexposed subtrees, and actual append/reuse are supported. Only initial slice-local data is used;
no visitor-exclusion, operation-success or poststate ownership premise occurs.
Protector registration and allocator/history iteration are separate stages. -/
theorem run (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) (mode : ChildrenVisitMode)
    (context : Context tree parent primary extras) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (before : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data tree location protections parent primary extras))
      offset (offset+len) tree.locations) :
    (read tree protections parentTag offset len mode).status = .Completed ∧
    (child tree protections parentTag newTag offset len mode).outcome = .ok () ∧
    Nonempty (Context (child tree protections parentTag newTag offset len mode).tree
      (GeneralBorrowFreshMetadataChildMutableSlot.index slot) primary extras) ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data (child tree protections parentTag newTag offset len mode).tree
        location protections (GeneralBorrowFreshMetadataChildMutableSlot.index slot) primary extras))
      offset (offset+len) (child tree protections parentTag newTag offset len mode).tree.locations ∧
    (child tree protections parentTag newTag offset len mode).tree.indexOfTag newTag = some (GeneralBorrowFreshMetadataChildMutableSlot.index slot) ∧
    (child tree protections parentTag newTag offset len mode).tree.locations.WellFormed ∧
    (child tree protections parentTag newTag offset len mode).tree.locations.size = tree.locations.size ∧
    (child tree protections parentTag newTag offset len mode).tree.nodes.data.size ≤ 4294967296 ∧
    GeneralBorrowGraph.RootsCover (child tree protections parentTag newTag offset len mode).tree := by
  have good := GeneralBorrowForestMutableSlice.access tree protections parentTag parent primary extras
    (Size.ofBytes offset) (Size.ofBytes len) .Read mode context parentTagPresent well fits offset (offset+len) before bounds
    (Nat.le_refl _) (Nat.le_refl _)
  let accessed := read tree protections parentTag offset len mode
  change accessed.status = .Completed ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data accessed.tree location protections parent primary extras))
      offset (offset+len) accessed.tree.locations ∧
    accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections mode
  change accessed.tree = {tree with locations := accessed.tree.locations} at frame
  have nodes : accessed.tree.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let depth := depth_on tree accessed.tree nodes context.depth
  let nextContext : Context accessed.tree parent primary extras := {
    anchorNode := context.anchorNode
    primaryNode := context.primaryNode
    depth := depth
    children := by rw [frame];exact context.children
    anchorPresent := by change accessed.tree.nodes.get parent = _;rw [nodes];exact context.anchorPresent
    primaryPresent := by rw [nodes];exact context.primaryPresent
    roots := by rw [frame];exact context.roots
    different := context.different
    unexposed := by intro index node present;rw [nodes] at present;exact context.unexposed index node present }
  have nextCovered : GeneralBorrowGraph.RootsCover accessed.tree := by rw [frame];exact covered
  have nextTag : accessed.tree.indexOfTag parentTag = some parent := by rw [frame];exact parentTagPresent
  have nextFresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact fresh
  let nextSlot := GeneralBorrowFreshMetadataChildMutableSlot.transport tree accessed.tree context.depth depth nodes mapping rfl parent slot
  have slotEq : GeneralBorrowFreshMetadataChildMutableSlot.index nextSlot = GeneralBorrowFreshMetadataChildMutableSlot.index slot :=
    GeneralBorrowFreshMetadataChildMutableSlot.transport_index tree accessed.tree context.depth depth nodes mapping rfl parent slot
  have nextFits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact fits
  have nextBounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  have result := GeneralBorrowForestProtectedConstructor.construct accessed.tree protections newTag parentTag parent primary extras offset len
    nextContext nextCovered nextTag nextFresh nextSlot nextFits nonzero good.2.2.1 nextBounds good.2.1
  let metadata := GeneralBorrowFreshMetadataChildMutableSlot.build accessed.tree depth nextContext.children nextCovered parentTag newTag parent context.anchorNode
    nextTag nextContext.anchorPresent nextFresh nextSlot offset len nonzero good.2.2.1 nextFits nextBounds
  refine ⟨good.1,result.1,?_,?_,?_,metadata.well,metadata.capacity.trans good.2.2.2,metadata.nodeFits,metadata.certificates.covered⟩
  · simpa only [slotEq,child,accessed] using result.2.1
  · simpa only [slotEq,child,accessed] using result.2.2
  · simpa only [slotEq,child,accessed,GeneralBorrowFreshMetadataChildMutableSlot.result] using metadata.lookup

end DuplicatePrefix.GeneralBorrowForestProtected
