import duplicate_prefix.GeneralBorrowForestAccessRange
import duplicate_prefix.GeneralBorrowFreshReborrowStages
import duplicate_prefix.GeneralBorrowCanonicalParentDepth
import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant

namespace DuplicatePrefix.GeneralBorrowForestSharedData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestAccessData
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def registered (protections : ProtectedTags) (newTag : BorTag) (isProtected : Bool) : ProtectedTags :=
  if isProtected then protections.insert newTag .StrongProtector else protections

/-- One positive shared reborrow's initial graph/allocator/range records.
The root schedule is in context and may contain arbitrary extra subtrees.
The per-location records refer to the actual registered protector map. -/
structure Data (tree : BorrowTree) (protections : ProtectedTags) (newTag : BorTag) (isProtected : Bool)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64) where
  context : Context tree parent primary extras
  parentTag : BorTag
  tagPresent : tree.indexOfTag parentTag = some parent
  fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag
  protectorFresh : GeneralBorrowProtector.Fresh tree newTag
  slot : Slot tree context.depth parent
  nonzero : len ≠ 0
  well : tree.locations.WellFormed
  bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat
  locations : GeneralRangeMapState.Every
    (fun location => Nonempty (LocationData tree location (registered protections newTag isProtected) parent primary extras .Read)) tree.locations

/-- Structural resources for a reusable general-root factory. The allocator
may contain an arbitrary consistent reusable pool. No root equality or access
success is a resource field. -/
structure Resources (tree : BorrowTree) where
  depth : GeneralBorrowExposure.ParentDepth tree.nodes
  children : GeneralBorrowGraph.ChildNodes tree
  allocator : GeneralBorrowGcAllocator.Invariant tree
  well : tree.locations.WellFormed
  room : tree.nodes.size + 4 ≤ 4294967295

/-- Select an actual append/reuse slot at any present primary-component
parent. Canonical depth normalization derives reuse slack from raw metadata.
The finite extra-root schedule and permissions/cache records are caller data. -/
def factory (tree : BorrowTree) (protections : ProtectedTags) (newTag : BorTag) (isProtected : Bool)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64)
    (resources : Resources tree) (context : Context tree parent primary extras)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (locations : GeneralRangeMapState.Every
      (fun location => Nonempty (LocationData tree location (registered protections newTag isProtected) parent primary extras .Read)) tree.locations) :
    Data tree protections newTag isProtected parent primary extras offset len := by
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

end DuplicatePrefix.GeneralBorrowForestSharedData
