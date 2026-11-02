import duplicate_prefix.GeneralBorrowForestSliceAccess
import duplicate_prefix.GeneralBorrowForestSharedData

namespace DuplicatePrefix.GeneralBorrowForestSliceShared
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowForestSharedData (registered Resources)
open GeneralBorrowFreshReadFrame
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- One positive shared reborrow's initial graph/allocator/range records.
The root schedule is in context and may contain arbitrary extra subtrees.
The per-location records refer to the actual registered protector map and are
required ONLY on the requested slice, with no ownership outside it. -/
structure Data (tree : BorrowTree) (protections : ProtectedTags) (newTag : BorTag) (isProtected : Bool)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) (mode : ChildrenVisitMode) where
  context : Context tree parent primary extras
  parentTag : BorTag
  tagPresent : tree.indexOfTag parentTag = some parent
  fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag
  protectorFresh : GeneralBorrowProtector.Fresh tree newTag
  slot : Slot tree context.depth parent
  nonzero : len ≠ 0
  well : tree.locations.WellFormed
  bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat
  locations : GeneralRangeMapOrigins.OwnedOn
    (fun location => Nonempty (GeneralBorrowForestModeAccess.LocationData tree location (registered protections newTag isProtected) parent primary extras .Read mode)) offset (offset+len) tree.locations


/-- Select an actual append/reuse slot at any present primary-component
parent. Canonical depth normalization derives reuse slack from raw metadata.
The finite extra-root schedule and slice-local permissions/cache records are caller data. -/
def factory (tree : BorrowTree) (protections : ProtectedTags) (newTag : BorTag) (isProtected : Bool)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) (mode : ChildrenVisitMode)
    (resources : Resources tree) (context : Context tree parent primary extras)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (locations : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestModeAccess.LocationData tree location (registered protections newTag isProtected) parent primary extras .Read mode)) offset (offset+len) tree.locations) :
    Data tree protections newTag isProtected parent primary extras offset len mode := by
  let depth := GeneralBorrowCanonicalParentDepth.normalize tree.nodes resources.depth
  have aligned := GeneralBorrowFreshStagePool.empty_aligned tree resources.allocator.accounting
  have fits : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295 := by
    intro empty
    rw [aligned empty]
    have room := resources.room
    change tree.nodes.data.size+4 ≤ _ at room
    omega
  let slot := GeneralBorrowCanonicalParentDepth.slot tree resources.depth parent context.anchorNode context.anchorPresent
    resources.allocator.pool aligned fits
  refine {
    context := {context with depth := depth,children := resources.children}
    parentTag := context.anchorNode.tag
    tagPresent := resources.allocator.nodeTags parent context.anchorNode context.anchorPresent
    fresh := fresh,protectorFresh := ?_,slot := slot,nonzero := nonzero,well := resources.well,bounds := bounds,locations := locations }
  intro row member same
  have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
  have lookup := resources.allocator.nodeTags row.1 row.2 present
  have absent : tree.tagMapping.get newTag = none := by
    unfold UniKeyMap.get
    rw [GeneralBorrowTagMap.fresh_find tree.tagMapping newTag fresh]
    rfl
  rw [same,absent] at lookup
  cases lookup


def read {tree : BorrowTree} {protections : ProtectedTags} {newTag : BorTag} {isProtected : Bool}
    {parent primary : UniIndex} {extras : List UniIndex} {offset len : UInt64} {mode : ChildrenVisitMode}
    (data : Data tree protections newTag isProtected parent primary extras offset len mode) :=
  tree.performBorrowAccessRange (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (registered protections newTag isProtected) mode

def child {tree : BorrowTree} {protections : ProtectedTags} {newTag : BorTag} {isProtected : Bool}
    {parent primary : UniIndex} {extras : List UniIndex} {offset len : UInt64} {mode : ChildrenVisitMode}
    (data : Data tree protections newTag isProtected parent primary extras offset len mode) :=
  (read data).tree.newChild (Size.ofBytes offset) (.concrete data.parentTag) newTag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected

/-- Actual registered-protector Read followed by the actual Frozen newChild,
with arbitrary finite extra unexposed foreign-owned subtrees and either real
append or reusable allocator slot. Every success fact is derived from initial
slice-local Data; none is a premise. No outside-window ownership is assumed.
Both normal-visitor modes are supported, including
SkipChildrenOfAccessed. This is a reborrow component, not yet FnEntry/fullcall. -/
theorem run (tree : BorrowTree) (protections : ProtectedTags) (newTag : BorTag) (isProtected : Bool)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) (mode : ChildrenVisitMode)
    (data : Data tree protections newTag isProtected parent primary extras offset len mode) :
    (read data).status = .Completed ∧ (child data).outcome = .ok () := by
  have good := GeneralBorrowForestSliceAccess.access tree (registered protections newTag isProtected) data.parentTag
    parent primary extras (Size.ofBytes offset) (Size.ofBytes len) .Read mode data.context data.tagPresent data.well
    offset (offset+len) data.locations data.bounds (Nat.le_refl _) (Nat.le_refl _)
  change (read data).status = .Completed ∧ (read data).tree.locations.WellFormed ∧
    (read data).tree.locations.size = tree.locations.size at good
  refine ⟨good.1,?_⟩
  let accessed := read data
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (registered protections newTag isProtected) mode
  change accessed.tree = {tree with locations := accessed.tree.locations} at frame
  have nodes : accessed.tree.nodes = tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  let depth := depth_on tree accessed.tree nodes data.context.depth
  have parentPresent : accessed.tree.nodeAt parent = some data.context.anchorNode := by
    change accessed.tree.nodes.get parent = _
    rw [nodes]
    exact data.context.anchorPresent
  have tagPresent : accessed.tree.tagMapping.get data.parentTag = some parent := by
    rw [mapping]
    exact data.tagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact data.fresh
  have bounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2];exact data.bounds
  change (accessed.tree.newChild (Size.ofBytes offset) (.concrete data.parentTag) newTag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected).outcome = .ok ()
  cases data.slot with
  | append noFree aligned fits =>
    apply GeneralBorrowFreshSharedChild.append_success accessed.tree depth data.parentTag newTag parent data.context.anchorNode
      tagPresent parentPresent fresh
    · simpa only [mapping] using noFree
    · simpa only [mapping,nodes] using aligned
    · simpa only [mapping] using fits
    · exact data.nonzero
    · exact good.2.1
    · exact bounds
  | reuse index available bounded vacant slack =>
    apply GeneralBorrowFreshSharedChild.reuse_success accessed.tree depth data.parentTag newTag parent data.context.anchorNode
      tagPresent parentPresent fresh index
    · simpa only [mapping] using available
    · simpa only [nodes] using bounded
    · simpa only [nodes] using vacant
    · simpa only [depth,depth_on,nodes] using slack
    · exact data.nonzero
    · exact good.2.1
    · exact bounds

end DuplicatePrefix.GeneralBorrowForestSliceShared
