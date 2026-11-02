import duplicate_prefix.GeneralBorrowExposedWildcardRange
import duplicate_prefix.GeneralBorrowPositiveWildcardConstructor
import duplicate_prefix.GeneralBorrowFreshReadFrame
namespace DuplicatePrefix.GeneralBorrowExposedWildcardReborrow
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposedWildcardRange
open DuplicatePrefix.GeneralBorrowPositiveWildcardConstructor
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual positive wildcard Read followed by protected reservation root
formation. The new node is a physical additional root, with a real permission
row installed throughout the requested slice. Initial wildcard reference data,
allocator resources and byte bounds derive both successes; neither operation's
success is a premise. Global protector registration remains the caller's stage. -/
theorem append (tree : BorrowTree) (protections : ProtectedTags)
    (primary : UniIndex) (primaryNode : TreeNode) (extras : List UniIndex) (nodes : UniIndex → TreeNode)
    (tag : BorTag) (offset len : UInt64)
    (roots : tree.roots = (primary::extras).toArray)
    (present : tree.nodes.get primary = some primaryNode) (leaf : primaryNode.children = #[])
    (exposed : primaryNode.isExposed = true) (short : tree.nodes.size < 65536)
    (well : tree.locations.WellFormed)
    (owned : GeneralRangeMapOrigins.OwnedOn (Ready tree protections primary extras nodes .Read) offset (offset+len) tree.locations)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) (nonzero : len ≠ 0)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (noFree : tree.tagMapping.deassigned.back? = none) (fits : tree.tagMapping.mapping.size ≤ 4294967295) :
    let read := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
    let inserted := read.tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) ⟨.ReservedFrz false,true,.None⟩) (.ReservedFrz false) true
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    read.status = .Completed ∧ inserted.outcome = .ok () ∧
      inserted.tree.roots = tree.roots.push index ∧
      inserted.tree.indexOfTag tag = some index ∧
      inserted.tree.nodeAt index = some (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) ∧
      inserted.tree.locations = (read.tree.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
        (fun _ location => {location with perms := location.perms.insert index ⟨.ReservedFrz false,true,.None⟩})).state := by
  let read := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
  have good := GeneralBorrowExposedWildcardRange.access tree protections primary primaryNode extras nodes
    (Size.ofBytes offset) (Size.ofBytes len) .Read .VisitChildrenOfAccessed roots present leaf exposed short well
    offset (offset+len) owned bounds (Nat.le_refl _) (Nat.le_refl _)
  have frame := GeneralBorrowFreshReadFrame.frame tree .wildcard (Size.ofBytes offset) (Size.ofBytes len)
    .Read protections .VisitChildrenOfAccessed
  change read.tree = {tree with locations := read.tree.locations} at frame
  have mapping : read.tree.tagMapping = tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  have rootFrame : read.tree.roots = tree.roots := by simpa only using congrArg BorrowTree.roots frame
  have nextFresh : GeneralBorrowTagMap.Fresh read.tree.tagMapping tag := by rw [mapping];exact fresh
  have nextNoFree : read.tree.tagMapping.deassigned.back? = none := by rw [mapping];exact noFree
  have nextFits : read.tree.tagMapping.mapping.size ≤ 4294967295 := by rw [mapping];exact fits
  have nextBounds : offset.toNat+len.toNat ≤ read.tree.locations.size.bytes.toNat := by rw [good.2.2];exact bounds
  have inserted := GeneralBorrowPositiveWildcardConstructor.append read.tree tag nextFresh nextNoFree nextFits
    (.ReservedFrz false) .None ⟨.ReservedFrz false,true,.None⟩ true rfl rfl rfl rfl rfl
    offset len nonzero good.2.1 nextBounds
  dsimp only
  change read.status = .Completed ∧ _
  rw [inserted]
  simp only [result,WildcardHitZeroConstructor.installed]
  rw [mapping,rootFrame]
  refine ⟨good.1,True.intro,rfl,?_,?_,rfl⟩
  · exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag fresh _ _
  · exact GeneralBorrowFreshLocation.get_same read.tree.nodes _ _
end DuplicatePrefix.GeneralBorrowExposedWildcardReborrow
