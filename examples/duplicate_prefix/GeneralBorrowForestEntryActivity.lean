import duplicate_prefix.GeneralBorrowForestArgumentCopy
import duplicate_prefix.GeneralBorrowForestMutableCleanRange
import duplicate_prefix.GeneralBorrowFreshMutableStages

namespace DuplicatePrefix.GeneralBorrowForestEntryActivity
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshReadFrame GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- INITIAL allocator-slot permission Clean derives that the real FnEntry
child's active permissions occur only inside its input slice. Vacancy alone is
not used as Clean. This handles all real normal/extra-root Read accesses and
both actual constructor allocator branches without success assumptions. -/
theorem child (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GeneralBorrowForestEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshMetadataChildMutableSlot.index data.slot) = none) tree.locations) :
    GeneralBorrowFreshActiveWithin.ActiveWithin (GeneralBorrowForestArgumentCopy.finalTree tree tracker parentTag offset len)
      (GeneralBorrowFreshMetadataChildMutableSlot.index data.slot) .Write offset (offset+len) := by
  let registered := tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector
  let accessed := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have owners := GeneralBorrowForestMutableRegister.registered tree tracker.global {} ⟨1,by decide⟩ tracker.global.nextPointerTag .StrongProtector
    data.parent data.primary data.extras data.tagFresh data.nodeTags data.globalUnheld offset (offset+len) data.owned
  have good := GeneralBorrowForestMutableSlice.access tree registered parentTag data.parent data.primary data.extras
    (Size.ofBytes offset) (Size.ofBytes len) .Read .VisitChildrenOfAccessed data.context data.tagPresent data.well data.nodeFits
    offset (offset+len) owners.2.2.2 bounds (Nat.le_refl _) (Nat.le_refl _)
  change accessed.status = .Completed ∧ GeneralRangeMapOrigins.OwnedOn
    (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data accessed.tree location registered data.parent data.primary data.extras))
    offset (offset+len) accessed.tree.locations ∧ accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  let index := GeneralBorrowFreshMetadataChildMutableSlot.index data.slot
  have vacant : tree.nodes.get index = none := by
    have empty := GeneralBorrowFreshMutableStages.slot_vacant tree data.context.depth data.parent data.slot
    cases chosen : data.slot <;> simpa only [index,GeneralBorrowFreshMetadataChildMutableSlot.index,GeneralBorrowFreshMutableStages.slot_index,chosen] using empty
  have cleanResult := GeneralBorrowForestMutableCleanRange.ranged tree registered parentTag data.parent data.primary index data.extras
    (Size.ofBytes offset) (Size.ofBytes len) .Read .VisitChildrenOfAccessed data.context data.nodeFits data.tagPresent vacant clean
    data.well offset (offset+len) owners.2.2.2 bounds (Nat.le_refl _) (Nat.le_refl _)
  have cleanAfter : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get index = none) accessed.tree.locations := cleanResult.2
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  change accessed.tree = {tree with locations := accessed.tree.locations} at framed
  have nodes : accessed.tree.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes framed
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping framed
  let depth := depth_on tree accessed.tree nodes data.context.depth
  have parentPresent : accessed.tree.nodeAt data.parent = some data.context.anchorNode := by change accessed.tree.nodes.get data.parent = _;rw [nodes];exact data.context.anchorPresent
  have tagPresent : accessed.tree.tagMapping.get parentTag = some data.parent := by rw [mapping];exact data.tagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping tracker.global.nextPointerTag := by rw [mapping];exact data.tagFresh
  have nextBounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  have fits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact data.nodeFits
  have parentOwners : GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned accessed.tree registered data.parent .Write)
      offset (offset+len) accessed.tree.locations := by
    intro position valid positive lower upper
    obtain ⟨localData⟩ := good.2.1 position valid positive lower upper
    exact ⟨⟨localData.base.forest⟩,localData.base.owned⟩
  cases chosen : data.slot with
  | append noFree aligned indexFits =>
    have noFreeAfter : accessed.tree.tagMapping.deassigned.back? = none := by rw [mapping];exact noFree
    have alignedAfter : accessed.tree.tagMapping.mapping.size = accessed.tree.nodes.data.size := by rw [mapping,nodes];exact aligned
    have fitsAfter : accessed.tree.tagMapping.mapping.size ≤ 4294967295 := by rw [mapping];exact indexFits
    have sameIndex : (⟨UInt32.ofNat accessed.tree.tagMapping.mapping.size⟩ : UniIndex) = index := by
      dsimp only [index]
      rw [chosen]
      simp only [GeneralBorrowFreshMetadataChildMutableSlot.index]
      rw [mapping]
    have cleanCtor : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get ⟨UInt32.ofNat accessed.tree.tagMapping.mapping.size⟩ = none) accessed.tree.locations := by rw [sameIndex];exact cleanAfter
    have constructed := GeneralBorrowFreshMutableWithin.append accessed.tree depth parentTag tracker.global.nextPointerTag data.parent data.context.anchorNode
      tagPresent parentPresent fresh noFreeAfter alignedAfter fitsAfter offset len nonzero good.2.2.1 nextBounds registered parentOwners cleanCtor
    simpa only [sameIndex,index,GeneralBorrowFreshMetadataChildMutableSlot.index,chosen,GeneralBorrowForestArgumentCopy.finalTree,accessed,registered,TypedBorrowSteps.registeredGlobal] using constructed.2.2
  | reuse candidate available bounded vacant slack =>
    have availableAfter : accessed.tree.tagMapping.deassigned.back? = some candidate := by rw [mapping];exact available
    have boundedAfter : candidate.toNat < accessed.tree.nodes.data.size := by rw [nodes];exact bounded
    have vacantAfter : accessed.tree.nodes.get candidate = none := by rw [nodes];exact vacant
    have slackAfter : depth.depth data.parent < accessed.tree.nodes.size := by change data.context.depth.depth data.parent < accessed.tree.nodes.size;rw [nodes];exact slack
    have cleanCtor : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get candidate = none) accessed.tree.locations := by
      simpa only [index,GeneralBorrowFreshMetadataChildMutableSlot.index,chosen] using cleanAfter
    have constructed := GeneralBorrowFreshMutableWithin.reuse accessed.tree depth parentTag tracker.global.nextPointerTag data.parent data.context.anchorNode
      tagPresent parentPresent fresh candidate availableAfter boundedAfter vacantAfter slackAfter fits offset len nonzero good.2.2.1 nextBounds registered parentOwners cleanCtor
    simpa only [index,GeneralBorrowFreshMetadataChildMutableSlot.index,chosen,GeneralBorrowForestArgumentCopy.finalTree,accessed,registered,TypedBorrowSteps.registeredGlobal] using constructed.2.2

end DuplicatePrefix.GeneralBorrowForestEntryActivity
