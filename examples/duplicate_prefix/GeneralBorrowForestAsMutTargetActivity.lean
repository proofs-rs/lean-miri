import duplicate_prefix.GeneralBorrowForestEntryActivity
import duplicate_prefix.GeneralBorrowFreshMutableTargetWithin
namespace DuplicatePrefix.GeneralBorrowForestAsMutTargetActivity
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshReborrowStages DuplicatePrefix.GeneralBorrowFreshReadFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
set_option autoImplicit false in
/-- Preserve an older mutable anchor's strong activity through the real
protected mutable Read/constructor stage, from initial data only. -/
theorem preserves_target (tree : BorrowTree) (protections : ProtectedTags)
    (parentTag newTag : BorTag) (offset len : UInt64)
    (data : GeneralBorrowForestEntryValidity.Data tree protections parentTag newTag offset len)
    (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (target : UniIndex) (lower upper : UInt64)
    (requestLower : lower.toNat ≤ offset.toNat) (requestUpper : (offset+len).toNat ≤ upper.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write lower upper) :
    let registered := protections.insert newTag .StrongProtector
    let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read registered .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    GeneralBorrowFreshActiveWithin.ActiveWithin child.tree target .Write lower upper := by
  let registered := protections.insert newTag .StrongProtector
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  let parent := data.parent
  let parentNode := data.context.anchorNode
  let slot := data.slot
  have well := data.well
  have parentPresent := data.context.anchorPresent
  have parentTagPresent := data.tagPresent
  have tagFresh := data.tagFresh
  have registeredData := GeneralBorrowForestMutableRegister.registered tree {nextPointerTag := newTag,protectedTags := protections} {} ⟨1,by decide⟩ newTag .StrongProtector
    data.parent data.primary data.extras data.tagFresh data.nodeTags data.globalUnheld offset (offset+len) data.owned
  have good := GeneralBorrowForestMutableSlice.access tree registered parentTag data.parent data.primary data.extras
    (Size.ofBytes offset) (Size.ofBytes len) .Read .VisitChildrenOfAccessed data.context data.tagPresent data.well data.nodeFits
    offset (offset+len) registeredData.2.2.2 bounds (Nat.le_refl _) (Nat.le_refl _)
  have readActive : GeneralBorrowFreshActiveWithin.ActiveWithin read.tree target .Write lower upper :=
    GeneralBorrowFreshActiveWithinAccess.normal tree parentTag (Size.ofBytes offset) (Size.ofBytes len) .Read
      registered .VisitChildrenOfAccessed target lower upper well bounds requestLower requestUpper active
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have nodeEq := congrArg BorrowTree.nodes framed
  have nodes : read.tree.nodes = tree.nodes := nodeEq
  have tagEq := congrArg BorrowTree.tagMapping framed
  have tags : read.tree.tagMapping = tree.tagMapping := tagEq
  have parentAfter : read.tree.nodeAt parent = some parentNode := by
    change read.tree.nodes.get parent = some parentNode
    rw [nodes]
    exact parentPresent
  have parentTagAfter : read.tree.tagMapping.get parentTag = some parent := by rw [tags];exact parentTagPresent
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping newTag := by rw [tags];exact tagFresh
  have boundsAfter : offset.toNat+len.toNat ≤ read.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  dsimp only
  cases slot with
  | append noFree aligned fits =>
    have noFreeAfter : read.tree.tagMapping.deassigned.back? = none := by rw [tags];exact noFree
    have alignedAfter : read.tree.tagMapping.mapping.size = read.tree.nodes.data.size := by rw [tags,nodes];exact aligned
    have fitsIndex : read.tree.tagMapping.mapping.size ≤ 4294967295 := by rw [tags];exact fits
    exact GeneralBorrowFreshMutableTargetWithin.append read.tree parentTag newTag parent parentNode parentTagAfter parentAfter
      freshAfter noFreeAfter alignedAfter fitsIndex offset len nonzero good.2.2.1 boundsAfter
      target lower upper requestLower requestUpper readActive
  | reuse candidate available bounded vacant slack =>
    have availableAfter : read.tree.tagMapping.deassigned.back? = some candidate := by rw [tags];exact available
    have boundedAfter : candidate.toNat < read.tree.nodes.data.size := by rw [nodes];exact bounded
    have vacantAfter : read.tree.nodes.get candidate = none := by rw [nodes];exact vacant
    exact GeneralBorrowFreshMutableTargetWithin.reuse read.tree parentTag newTag parent parentNode parentTagAfter parentAfter
      freshAfter candidate availableAfter boundedAfter vacantAfter offset len nonzero good.2.2.1 boundsAfter
      target lower upper requestLower requestUpper readActive
end DuplicatePrefix.GeneralBorrowForestAsMutTargetActivity
