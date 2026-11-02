import duplicate_prefix.GeneralBorrowForestSliceShared
import duplicate_prefix.GeneralBorrowForestSliceOwner
import duplicate_prefix.GeneralBorrowSharedConstructorReadSlot
import duplicate_prefix.GeneralBorrowFreshMetadataChildSlot

namespace DuplicatePrefix.GeneralBorrowForestSliceSharedOwner
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
open GeneralBorrowForestSharedData (Resources)
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowFreshReadFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Build actual append/reuse constructor data from slice-local initial owner
records. The empty protector map selects the unprotected shared protocol. -/
def factory (tree : BorrowTree) (newTag : BorTag) (parent primary : UniIndex) (extras : List UniIndex)
    (offset len : UInt64) (mode : ChildrenVisitMode)
    (resources : Resources tree) (context : Context tree parent primary extras)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (locations : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestSliceOwner.InputLocation tree location {} parent primary extras .Read .Read mode))
      offset (offset+len) tree.locations) :
    GeneralBorrowForestSliceShared.Data tree {} newTag false parent primary extras offset len mode :=
  GeneralBorrowForestSliceShared.factory tree {} newTag false parent primary extras offset len mode resources context fresh nonzero bounds (by
    intro index valid positive beforeUpper afterLower
    obtain ⟨input⟩ := locations index valid positive beforeUpper afterLower
    exact ⟨input.data⟩)

/-- Real unprotected Read followed by the real Frozen constructor preserves the
parent's slice-local Read ownership in the FINAL constructed tree, for append
and reuse, arbitrary finite extra unexposed subtrees, and either visitor mode.
All success and poststate facts follow from initial records. -/
theorem run (tree : BorrowTree) (newTag : BorTag) (parent primary : UniIndex) (extras : List UniIndex)
    (offset len : UInt64) (mode : ChildrenVisitMode)
    (resources : Resources tree) (context : Context tree parent primary extras)
    (covered : GeneralBorrowGraph.RootsCover tree)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (locations : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestSliceOwner.InputLocation tree location {} parent primary extras .Read .Read mode))
      offset (offset+len) tree.locations) :
    let data := factory tree newTag parent primary extras offset len mode resources context fresh nonzero bounds locations
    (GeneralBorrowForestSliceShared.read data).status = .Completed ∧
    (GeneralBorrowForestSliceShared.child data).outcome = .ok () ∧
    GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned (GeneralBorrowForestSliceShared.child data).tree {} parent .Read)
      offset (offset+len) (GeneralBorrowForestSliceShared.child data).tree.locations := by
  dsimp only
  let data := factory tree newTag parent primary extras offset len mode resources context fresh nonzero bounds locations
  have fits : tree.nodes.data.size ≤ 4294967296 := by
    have room := resources.room
    change tree.nodes.data.size+4 ≤ _ at room
    omega
  have good := GeneralBorrowForestSliceShared.run tree {} newTag false parent primary extras offset len mode data
  have accessedGood := GeneralBorrowForestSliceOwner.access tree {} data.parentTag parent primary extras
    (Size.ofBytes offset) (Size.ofBytes len) .Read .Read mode data.context data.tagPresent data.well fits (fun same => same)
    offset (offset+len) locations data.bounds (Nat.le_refl _) (Nat.le_refl _)
  change (GeneralBorrowForestSliceShared.read data).status = .Completed ∧
    GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned (GeneralBorrowForestSliceShared.read data).tree {} parent .Read)
      offset (offset+len) (GeneralBorrowForestSliceShared.read data).tree.locations ∧
    (GeneralBorrowForestSliceShared.read data).tree.locations.WellFormed ∧
    (GeneralBorrowForestSliceShared.read data).tree.locations.size = tree.locations.size at accessedGood
  let accessed := GeneralBorrowForestSliceShared.read data
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read {} mode
  change accessed.tree = {tree with locations := accessed.tree.locations} at frame
  have nodes : accessed.tree.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let depth := depth_on tree accessed.tree nodes data.context.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [frame];exact data.context.children
  have coverage : GeneralBorrowGraph.RootsCover accessed.tree := by rw [frame];exact covered
  have present : accessed.tree.nodeAt parent = some data.context.anchorNode := by
    change accessed.tree.nodes.get parent = _
    rw [nodes]
    exact data.context.anchorPresent
  have tag : accessed.tree.indexOfTag data.parentTag = some parent := by
    change accessed.tree.tagMapping.get _ = _
    rw [mapping]
    exact data.tagPresent
  have newFresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact fresh
  let slot := GeneralBorrowFreshMetadataChildSlot.transport tree accessed.tree data.context.depth depth nodes mapping rfl parent data.slot
  have newBounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [accessedGood.2.2.2];exact bounds
  have newFits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact fits
  refine ⟨good.1,good.2,?_⟩
  exact GeneralBorrowSharedConstructorReadSlot.owned accessed.tree depth children coverage data.parentTag newTag parent data.context.anchorNode
    tag present newFresh slot offset len nonzero accessedGood.2.2.1 newBounds newFits parent ⟨data.context.anchorNode,present⟩ accessedGood.2.1

end DuplicatePrefix.GeneralBorrowForestSliceSharedOwner
