import duplicate_prefix.GeneralBorrowProtectedChildOrder
import duplicate_prefix.GeneralBorrowFreshSharedTargetWithin
import duplicate_prefix.GeneralBorrowFreshDefaultTargetWithin
import duplicate_prefix.GeneralBorrowFreshMutableTargetWithin
import duplicate_prefix.GeneralBorrowActiveWithinRelease
namespace DuplicatePrefix.GeneralBorrowRawTargetActivity
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Actual constructor preserves any old mutable anchor's activity. Allocator
append/reuse is derived from current runtime data; no operation success or
post-state activity is supplied. -/
theorem shared (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295) (isProtected : Bool)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (target : UniIndex) (lower upper : UInt64)
    (requestLower : lower.toNat ≤ offset.toNat) (requestUpper : (offset+len).toNat ≤ upper.toNat)
    (active : ActiveWithin tree target .Write lower upper) :
    ActiveWithin (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected).tree target .Write lower upper := by
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    exact GeneralBorrowFreshSharedTargetWithin.append tree parentTag newTag parent parentNode tagged present fresh
      noFree aligned fits isProtected offset len nonzero runtime.formed.well bounds target lower upper requestLower requestUpper active
  | reuse child available valid vacant slack =>
    exact GeneralBorrowFreshSharedTargetWithin.reuse tree parentTag newTag parent parentNode tagged present fresh
      child available valid vacant isProtected offset len nonzero runtime.formed.well bounds target lower upper requestLower requestUpper active

/-- Actual constructor preserves any old mutable anchor's activity. Allocator
append/reuse is derived from current runtime data; no operation success or
post-state activity is supplied. -/
theorem default_child (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (target : UniIndex) (lower upper : UInt64)
    (requestLower : lower.toNat ≤ offset.toNat) (requestUpper : (offset+len).toNat ≤ upper.toNat)
    (active : ActiveWithin tree target .Write lower upper) :
    ActiveWithin (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree target .Write lower upper := by
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    exact GeneralBorrowFreshDefaultTargetWithin.append tree parentTag newTag parent parentNode tagged present fresh
      noFree aligned fits offset len nonzero runtime.formed.well bounds target lower upper requestLower requestUpper active
  | reuse child available valid vacant slack =>
    exact GeneralBorrowFreshDefaultTargetWithin.reuse tree parentTag newTag parent parentNode tagged present fresh
      child available valid vacant offset len nonzero runtime.formed.well bounds target lower upper requestLower requestUpper active

/-- Actual constructor preserves any old mutable anchor's activity. Allocator
append/reuse is derived from current runtime data; no operation success or
post-state activity is supplied. -/
theorem protected_child (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (target : UniIndex) (lower upper : UInt64)
    (requestLower : lower.toNat ≤ offset.toNat) (requestUpper : (offset+len).toNat ≤ upper.toNat)
    (active : ActiveWithin tree target .Write lower upper) :
    ActiveWithin (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree target .Write lower upper := by
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    exact GeneralBorrowFreshMutableTargetWithin.append tree parentTag newTag parent parentNode tagged present fresh
      noFree aligned fits offset len nonzero runtime.formed.well bounds target lower upper requestLower requestUpper active
  | reuse child available valid vacant slack =>
    exact GeneralBorrowFreshMutableTargetWithin.reuse tree parentTag newTag parent parentNode tagged present fresh
      child available valid vacant offset len nonzero runtime.formed.well bounds target lower upper requestLower requestUpper active

end DuplicatePrefix.GeneralBorrowRawTargetActivity
