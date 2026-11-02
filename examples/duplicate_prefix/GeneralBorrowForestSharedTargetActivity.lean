import duplicate_prefix.GeneralBorrowFreshSharedTargetWithin
import duplicate_prefix.GeneralBorrowFreshSharedWithinStages
import duplicate_prefix.GeneralBorrowForestMixedRegister
import duplicate_prefix.GeneralBorrowForestMixedSlice
import duplicate_prefix.GeneralBorrowForestForeignCleanRange
namespace DuplicatePrefix.GeneralBorrowForestSharedTargetActivity
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralRangeMapOrigins GeneralBorrowFreshReleaseMixed GeneralBorrowFreshMixedChild GeneralBorrowFreshReborrowStages GeneralBorrowFreshReadFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem preserves_target (tree : BorrowTree) (protections : ProtectedTags) (isProtected : Bool)
    (parentTag newTag : BorTag) (parent primary : UniIndex) (extras : List UniIndex)
    (context : GeneralBorrowForestAccessData.Context tree parent primary extras)
    (covered : GeneralBorrowGraph.RootsCover tree) (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (protectorFresh : GeneralBorrowProtector.Fresh tree newTag)
    (nodeFits : tree.nodes.data.size ≤ 4294967296) (slot : Slot tree context.depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) (writable : Nat → Bool)
    (owned : OwnedOn (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data tree location protections parent primary extras writable)) offset (offset+len) tree.locations)
    (target : UniIndex) (lower upper : UInt64)
    (requestLower : lower.toNat ≤ offset.toNat) (requestUpper : (offset+len).toNat ≤ upper.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper) :
    let registered := if isProtected then protections.insert newTag .StrongProtector else protections
    let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read registered .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected
    GeneralBorrowFreshActiveWithin.ActiveWithin child.tree target .Write lower upper := by
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
  have readActive : GeneralBorrowFreshActiveWithin.ActiveWithin read.tree target .Write lower upper :=
    GeneralBorrowFreshActiveWithinAccess.normal tree parentTag (Size.ofBytes offset) (Size.ofBytes len) .Read
      registered .VisitChildrenOfAccessed target lower upper well bounds requestLower requestUpper active
  dsimp only
  cases slot with
  | append noFree aligned fits =>
    have noFreeAfter : read.tree.tagMapping.deassigned.back? = none := by rw [tags];exact noFree
    have alignedAfter : read.tree.tagMapping.mapping.size = read.tree.nodes.data.size := by rw [tags,nodes];exact aligned
    have fitsAfter : read.tree.tagMapping.mapping.size ≤ 4294967295 := by rw [tags];exact fits
    exact GeneralBorrowFreshSharedTargetWithin.append read.tree parentTag newTag parent parentNode parentTagAfter parentAfter
      freshAfter noFreeAfter alignedAfter fitsAfter isProtected offset len nonzero good.2.2.1 boundsAfter target lower upper requestLower requestUpper readActive
  | reuse candidate available bounded vacant slack =>
    have availableAfter : read.tree.tagMapping.deassigned.back? = some candidate := by rw [tags];exact available
    have boundedAfter : candidate.toNat < read.tree.nodes.data.size := by rw [nodes];exact bounded
    have vacantAfter : read.tree.nodes.get candidate = none := by rw [nodes];exact vacant
    exact GeneralBorrowFreshSharedTargetWithin.reuse read.tree parentTag newTag parent parentNode parentTagAfter parentAfter
      freshAfter candidate availableAfter boundedAfter vacantAfter isProtected offset len nonzero good.2.2.1 boundsAfter target lower upper requestLower requestUpper readActive
end DuplicatePrefix.GeneralBorrowForestSharedTargetActivity
