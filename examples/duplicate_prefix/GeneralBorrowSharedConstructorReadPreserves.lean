import duplicate_prefix.GeneralBorrowSharedConstructorReadRange
import duplicate_prefix.GeneralBorrowFreshMetadataChildShared
import duplicate_prefix.GeneralBorrowFreshMetadataChildSharedReuse
import duplicate_prefix.GeneralBorrowFreshOwnedOn

namespace DuplicatePrefix.GeneralBorrowSharedConstructorReadPreserves
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

namespace Append
open GeneralBorrowFreshMetadataChildShared

/-- The actual shared constructor and ancestor Read-SIFA update preserve an
arbitrary pre-existing Read anchor throughout its selected range under {}. -/
theorem owned (input : Input) (target : UniIndex)
    (before : OwnedOn (GeneralBorrowRange.LocationOwned input.tree {} target .Read)
      input.offset (input.offset+input.len) input.tree.locations) :
    OwnedOn (GeneralBorrowRange.LocationOwned (result input) {} target .Read)
      input.offset (input.offset+input.len) (result input).locations := by
  have installed := GeneralBorrowSharedConstructorReadRange.append_ranged_owned input.tree (index input) input.parent target input.parentNode input.newTag
    (at_end input) input.parentPresent (Size.ofBytes input.offset) (Size.ofBytes input.len) input.well input.bounds before
  have staged : OwnedOn (GeneralBorrowRange.LocationOwned (stage input) {} target .Read)
      input.offset (input.offset+input.len) (stage input).locations := by
    exact installed
  exact GeneralBorrowFreshOwnedOn.shape_preserves (stage input) (result input) (shape input) {} target .Read input.offset (input.offset+input.len) staged
end Append

namespace Reuse
open GeneralBorrowFreshMetadataChildSharedReuse

/-- An actual shared reuse also preserves every nonreused old Read anchor;
the vacancy/presence bank invariant derives the required index inequality. -/
theorem owned (input : Input) (target : UniIndex) (different : target ≠ input.index)
    (fits : input.tree.nodes.data.size ≤ 4294967296)
    (before : OwnedOn (GeneralBorrowRange.LocationOwned input.tree {} target .Read)
      input.offset (input.offset+input.len) input.tree.locations) :
    OwnedOn (GeneralBorrowRange.LocationOwned (result input) {} target .Read)
      input.offset (input.offset+input.len) (result input).locations := by
  have installed := GeneralBorrowSharedConstructorReadRange.reuse_ranged_owned input.tree input.index input.parent target input.parentNode input.newTag
    input.valid input.vacant fits input.parentPresent different
    (Size.ofBytes input.offset) (Size.ofBytes input.len) input.well input.bounds before
  have staged : OwnedOn (GeneralBorrowRange.LocationOwned (stage input) {} target .Read)
      input.offset (input.offset+input.len) (stage input).locations := by
    exact installed
  exact GeneralBorrowFreshOwnedOn.shape_preserves (stage input) (result input) (shape input) {} target .Read input.offset (input.offset+input.len) staged
end Reuse

end DuplicatePrefix.GeneralBorrowSharedConstructorReadPreserves
