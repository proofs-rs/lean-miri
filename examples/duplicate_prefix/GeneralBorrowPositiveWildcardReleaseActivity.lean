import duplicate_prefix.GeneralBorrowScopedDefaultReleaseActivity
import duplicate_prefix.GeneralBorrowPositiveWildcardConstructor
import duplicate_prefix.GeneralBorrowFreshRangeFrame
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardReleaseActivity
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

theorem source (tree : BorrowTree) (mapping : UniKeyMap BorTag) (index : UniIndex) (tag : BorTag)
    (capacity : UInt64) (positive : (0:UInt64)<capacity) (well : tree.locations.WellFormed)
    (size : tree.locations.size.bytes=capacity) :
    let after := GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None GeneralBorrowFreshChild.inside 0 capacity
    GeneralBorrowFreshReleaseLoop.ActiveOn after index .Read 0 capacity ∧
    (∀ position (valid : position<after.locations.entries.size) state,
      after.locations.entries[position].data.perms.get index=some state → state.accessed=true →
      ∀ kind,state.permission.associatedAccess=some kind → kind=.Read) := by
  have bounds : (0:UInt64).toNat+capacity.toNat≤tree.locations.size.bytes.toNat := by rw [size];simp
  let modify := fun (_ : ByteRange) (location : LocationTree)=>{location with perms:=location.perms.insert index GeneralBorrowFreshChild.inside}
  have geometry := GeneralBorrowFreshRangeFrame.modifyRange_frame tree.locations (Size.ofBytes 0) (Size.ofBytes capacity) modify well bounds
  exact GeneralBorrowScopedDefaultReleaseActivity.formed _ index capacity (UInt64.lt_iff_toNat_lt.mp positive) geometry.1
    (geometry.2.trans size) (by
      simpa only [GeneralBorrowPositiveWildcardConstructor.result,Size.ofBytes,UInt64.zero_add] using (GeneralBorrowWildcardRootInstalled.installed tree.locations index GeneralBorrowFreshChild.inside (Size.ofBytes 0) (Size.ofBytes capacity) well bounds))
end DuplicatePrefix.GeneralBorrowPositiveWildcardReleaseActivity
