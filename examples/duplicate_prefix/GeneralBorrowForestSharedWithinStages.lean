import duplicate_prefix.GeneralBorrowFreshSharedWithinStages
import duplicate_prefix.GeneralBorrowForestMixedRegister
import duplicate_prefix.GeneralBorrowForestMixedSlice
import duplicate_prefix.GeneralBorrowForestForeignCleanRange
namespace DuplicatePrefix.GeneralBorrowForestSharedWithinStages
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralRangeMapOrigins GeneralBorrowFreshReleaseMixed GeneralBorrowFreshMixedChild GeneralBorrowFreshReborrowStages GeneralBorrowFreshReadFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem borrow (tree : BorrowTree) (protections : ProtectedTags) (isProtected : Bool)
    (parentTag newTag : BorTag) (parent primary : UniIndex) (extras : List UniIndex)
    (context : GeneralBorrowForestAccessData.Context tree parent primary extras)
    (covered : GeneralBorrowGraph.RootsCover tree) (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (protectorFresh : GeneralBorrowProtector.Fresh tree newTag)
    (nodeFits : tree.nodes.data.size ≤ 4294967296) (slot : Slot tree context.depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) (writable : Nat → Bool)
    (owned : OwnedOn (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data tree location protections parent primary extras writable)) offset (offset+len) tree.locations)
    (clean : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshSharedWithinStages.slot_index slot) = none) tree.locations) :
    let registered := if isProtected then protections.insert newTag .StrongProtector else protections
    let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read registered .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected
    read.status = .Completed ∧ child.outcome = .ok () ∧
      OwnedOn (Combined child.tree registered (GeneralBorrowFreshSharedWithinStages.slot_index slot) (extend writable (GeneralBorrowFreshSharedWithinStages.slot_index slot).toNat))
        offset (offset+len) child.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin child.tree (GeneralBorrowFreshSharedWithinStages.slot_index slot) .Read offset (offset+len) := by
  let registered := if isProtected then protections.insert newTag .StrongProtector else protections
  let index := GeneralBorrowFreshSharedWithinStages.slot_index slot
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  let depth := context.depth
  let parentNode := context.anchorNode
  have parentPresent : tree.nodeAt parent = some parentNode := context.anchorPresent
  have registeredOwners : OwnedOn (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data tree location registered parent primary extras writable)) offset (offset+len) tree.locations := by
    cases isProtected with
    | false => exact owned
    | true =>
      intro position valid positive start stop
      obtain ⟨data⟩ := owned position valid positive start stop
      exact ⟨GeneralBorrowForestMixedRegister.protect tree _ protections parent primary extras writable newTag .StrongProtector
        (fun index node present => protectorFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present))) data⟩
  have readOwners : OwnedOn (fun location => Nonempty (GeneralBorrowForestForeignAccess.LocationData tree location registered parent primary extras .Read)) offset (offset+len) tree.locations := by
    intro position valid positive start stop
    obtain ⟨data⟩ := registeredOwners position valid positive start stop
    exact ⟨data.base⟩
  have forestGood := GeneralBorrowForestMixedSlice.access tree registered parentTag parent primary extras (Size.ofBytes offset) (Size.ofBytes len)
    writable .VisitChildrenOfAccessed context parentTagPresent well nodeFits offset (offset+len) registeredOwners bounds (Nat.le_refl _) (Nat.le_refl _)
  have combined : OwnedOn (Combined read.tree registered parent writable) offset (offset+len) read.tree.locations := by
    intro position valid positive start stop
    obtain ⟨data⟩ := forestGood.2.1 position valid positive start stop
    exact ⟨⟨⟨data.base.forest⟩,data.base.owned⟩,data.mixed⟩
  have good : read.status = .Completed ∧ OwnedOn (Combined read.tree registered parent writable) offset (offset+len) read.tree.locations ∧
      read.tree.locations.WellFormed ∧ read.tree.locations.size = tree.locations.size :=
    ⟨forestGood.1,combined,forestGood.2.2.1,forestGood.2.2.2⟩
  have cleanResult := GeneralBorrowForestForeignCleanRange.ranged tree registered parentTag parent primary index extras (Size.ofBytes offset) (Size.ofBytes len)
    .VisitChildrenOfAccessed context nodeFits parentTagPresent
    (GeneralBorrowFreshSharedWithinStages.slot_vacant tree depth parent slot) clean well offset (offset+len) readOwners bounds (Nat.le_refl _) (Nat.le_refl _)
  have cleanAfter : Every (fun location : LocationTree => location.perms.get index = none) read.tree.locations := cleanResult.2
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have nodeEq := congrArg BorrowTree.nodes framed
  have nodes : read.tree.nodes = tree.nodes := nodeEq
  have tagEq := congrArg BorrowTree.tagMapping framed
  have tags : read.tree.tagMapping = tree.tagMapping := tagEq
  let readDepth := depth_on tree read.tree nodes depth
  have parentAfter : read.tree.nodeAt parent = some parentNode := by
    change read.tree.nodes.get parent = some parentNode
    rw [nodes]
    exact parentPresent
  have parentTagAfter : read.tree.tagMapping.get parentTag = some parent := by rw [tags];exact parentTagPresent
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping newTag := by rw [tags];exact tagFresh
  have boundsAfter : offset.toNat+len.toNat ≤ read.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  have fitsAfter : read.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact nodeFits
  dsimp only
  refine ⟨good.1,?_⟩
  cases slot with
  | append noFree aligned fits =>
    have noFreeAfter : read.tree.tagMapping.deassigned.back? = none := by rw [tags];exact noFree
    have alignedAfter : read.tree.tagMapping.mapping.size = read.tree.nodes.data.size := by rw [tags,nodes];exact aligned
    have fitsIndex : read.tree.tagMapping.mapping.size ≤ 4294967295 := by rw [tags];exact fits
    have sameIndex : (⟨UInt32.ofNat read.tree.tagMapping.mapping.size⟩ : UniIndex) = index := by
      dsimp only [index,GeneralBorrowFreshSharedWithinStages.slot_index]
      rw [tags]
    have cleanCtor : Every (fun location : LocationTree => location.perms.get ⟨UInt32.ofNat read.tree.tagMapping.mapping.size⟩ = none) read.tree.locations := by
      rw [sameIndex]
      exact cleanAfter
    have constructed := GeneralBorrowFreshMixedWithin.append read.tree readDepth parentTag newTag parent parentNode parentTagAfter parentAfter
      freshAfter noFreeAfter alignedAfter fitsIndex isProtected offset len nonzero good.2.2.1 boundsAfter registered writable good.2.1 cleanCtor
    simpa only [sameIndex,index] using constructed
  | reuse candidate available bounded vacant slack =>
    have availableAfter : read.tree.tagMapping.deassigned.back? = some candidate := by rw [tags];exact available
    have boundedAfter : candidate.toNat < read.tree.nodes.data.size := by rw [nodes];exact bounded
    have vacantAfter : read.tree.nodes.get candidate = none := by rw [nodes];exact vacant
    have slackAfter : readDepth.depth parent < read.tree.nodes.size := by
      change depth.depth parent < read.tree.nodes.size
      rw [nodes]
      exact slack
    have constructed := GeneralBorrowFreshMixedWithin.reuse read.tree readDepth parentTag newTag parent parentNode parentTagAfter parentAfter
      freshAfter candidate availableAfter boundedAfter vacantAfter slackAfter fitsAfter isProtected offset len nonzero good.2.2.1 boundsAfter
      registered writable good.2.1 cleanAfter
    simpa only [index,GeneralBorrowFreshSharedWithinStages.slot_index] using constructed
end DuplicatePrefix.GeneralBorrowForestSharedWithinStages
