import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedRun
import duplicate_prefix.GeneralBorrowFreshSharedTargetWithin
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
import duplicate_prefix.GeneralBorrowExposedScopedSharedPathMetadata
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedTargetActivity
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildShared GeneralBorrowFreshActiveWithin
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
/-- A real bounded Read/shared constructor retains an older target's outside
inactivity. Only initial raw resources/activity and interval arithmetic enter. -/
theorem preserve {profileMode : ProfileMode} (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat→Bool) (raw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor input protections selected head tail writable profileMode)
    (target : UniIndex) (lower upper : UInt64)
    (requestLower : lower.toNat≤input.offset.toNat) (requestUpper : (input.offset+input.len).toNat≤upper.toNat)
    (active : ActiveWithin input.tree target .Write lower upper) :
    ActiveWithin (GeneralBorrowExposedScopedSharedPathMetadata.child input protections .VisitChildrenOfAccessed)
      target .Write lower upper := by
  have readActive := GeneralBorrowFreshActiveWithinAccess.normal input.tree input.parentTag (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read protections .VisitChildrenOfAccessed target lower upper input.well input.bounds requestLower requestUpper active
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedInactiveWritableSharedRun.prepare_mode input protections selected head tail writable raw
  have preparedActive : ActiveWithin prepared.tree target .Write lower upper := by rw [treeEq];exact readActive
  have next := GeneralBorrowFreshSharedTargetWithin.append prepared.tree prepared.parentTag prepared.newTag prepared.parent prepared.parentNode
    prepared.parentTagPresent prepared.parentPresent prepared.fresh prepared.noFree prepared.aligned prepared.fits prepared.isProtected
    prepared.offset prepared.len prepared.nonzero prepared.well prepared.bounds target lower upper
    (by rw [offsetEq];exact requestLower) (by rw [offsetEq,lenEq];exact requestUpper) preparedActive
  simpa only [GeneralBorrowExposedScopedSharedPathMetadata.child,treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq] using next
end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedTargetActivity
