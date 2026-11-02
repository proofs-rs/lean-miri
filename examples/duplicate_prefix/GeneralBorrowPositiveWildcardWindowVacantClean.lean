import duplicate_prefix.GeneralBorrowPositiveWildcardWindowOriginalInput
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowArgumentCopy
import duplicate_prefix.GeneralBorrowSparseExposedLeafCleanRange
import duplicate_prefix.GeneralBorrowPositiveWildcardVacantClean
import duplicate_prefix.GeneralBorrowFreshReadFrame
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowVacantClean
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.DataStructures
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
/-- Allocation-wide vacant permissions survive the real window wildcard Read
and FnEntry constructor, from initial cleanliness alone. -/
theorem preserves (s : GeneralBorrowPositiveWildcardWindowOriginalInput.Base)
    (clean : GeneralBorrowGcVacantClean.VacantClean s.entry.allocation.extra) :
    GeneralBorrowGcVacantClean.VacantClean (GeneralBorrowPositiveWildcardWindowArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.offset s.len) := by
  let tree:=s.entry.allocation.extra
  let protections:=(TypedBorrowSteps.registeredGlobal s.tracker s.tracker.global.nextPointerTag).protectedTags
  let read:=tree.performBorrowAccessRange .wildcard (Size.ofBytes s.offset) (Size.ofBytes s.len) .Read protections .VisitChildrenOfAccessed
  have bounds : s.offset.toNat+s.len.toNat≤tree.locations.size.bytes.toNat := by rw [s.allocationCapacity];exact s.bounds
  have owned : GeneralRangeMapOrigins.OwnedOn (fun location=>GeneralBorrowSparseExposedLeafState.Raw tree location protections) s.offset (s.offset+s.len) tree.locations := by
    intro position valid _ _ _;exact s.sourceRaw position valid
  have result:=GeneralBorrowSparseExposedLeafRange.access tree protections s.head s.extraRoots s.leafGeometry (Size.ofBytes s.offset) (Size.ofBytes s.len)
    .Read .VisitChildrenOfAccessed s.initialState.well s.offset (s.offset+s.len) owned bounds (Nat.le_refl _) (Nat.le_refl _)
  have frame : read.tree={tree with locations:=read.tree.locations} := GeneralBorrowFreshReadFrame.frame tree .wildcard (Size.ofBytes s.offset)
    (Size.ofBytes s.len) .Read protections .VisitChildrenOfAccessed
  have nodes : read.tree.nodes=tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have capacity : read.tree.locations.size=tree.locations.size := result.2.2.2
  have readClean : GeneralBorrowGcVacantClean.VacantClean read.tree := by
    intro query vacant
    have old : tree.nodes.get query=none := by rw [←nodes];exact vacant
    exact (GeneralBorrowSparseExposedLeafCleanRange.ranged tree protections s.head query s.extraRoots s.leafGeometry (Size.ofBytes s.offset) (Size.ofBytes s.len)
      .Read .VisitChildrenOfAccessed old (clean query old) s.initialState.well s.offset (s.offset+s.len) owned bounds
      (Nat.le_refl _) (Nat.le_refl _)).2
  have nextBounds : s.offset.toNat+s.len.toNat≤read.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  exact GeneralBorrowPositiveWildcardVacantClean.preserves read.tree _ _ _ _ _ _ _ _ result.2.2.1 nextBounds readClean
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowVacantClean
