import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedConstructor
import duplicate_prefix.GeneralBorrowExposedScopedSharedActivity
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadRelease
import duplicate_prefix.GeneralBorrowFreshSharedGeometry
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometry
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedInactiveWritableSharedConstructor (ResourcesFor)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Real shared child formation and its real protector-end callbacks are joined
from initial resources and a clean allocator slot. Activity, child contracts,
release success and final partition geometry are all derived. -/
theorem release {profileMode : ProfileMode} (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : ResourcesFor input protections selected head tail writable profileMode)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index input) = none) input.tree.locations) :
    let child := result input
    let released := child.releaseProtector input.newTag protections
    released.status = .Released ∧ released.tree = {child with locations := released.tree.locations} ∧
      GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data released.tree location protections
        (index input) selected head tail (fun position => raw.component.support position ∨ position = (index input).toNat)
        (GeneralBorrowFreshMixedChild.extend writable (index input).toNat)))
        input.offset (input.offset+input.len) released.tree.locations ∧
      released.tree.locations.WellFormed ∧ released.tree.locations.size = input.tree.locations.size := by
  let metadata := GeneralBorrowFreshMetadataChildShared.append input
  let child := result input
  obtain ⟨success,context,owned⟩ := GeneralBorrowExposedScopedInactiveWritableSharedConstructor.construct_mode input protections selected head tail writable raw
  have geometry := GeneralBorrowFreshSharedGeometry.append_frame input
  have activity := GeneralBorrowExposedScopedSharedActivity.append input.tree input.depth input.parentTag input.newTag input.parent input.parentNode
    input.parentTagPresent input.parentPresent input.fresh input.noFree input.aligned input.fits input.isProtected input.offset input.len
    input.nonzero input.well input.bounds clean
  have active := GeneralBorrowFreshActiveWithin.active_on child (index input) .Read input.offset (input.offset+input.len) geometry.1 activity
  have fits : child.nodes.data.size ≤ 4294967296 := by
    change child.nodes.size ≤ 4294967296
    rw [metadata.size]
    have bound := raw.room
    omega
  have hidden : context.anchorNode.isExposed = false := by
    obtain ⟨node,present,tag,parent,children,permission,exposed⟩ := metadata.newNode
    have same := Option.some.inj (context.anchorPresent.symm.trans present)
    rw [same]
    exact exposed
  have done := GeneralBorrowExposedScopedInactiveWritableReadRelease.release child protections input.newTag (index input) selected head tail context
    (fun position => raw.component.support position ∨ position = (index input).toNat)
    (GeneralBorrowFreshMixedChild.extend writable (index input).toNat) input.offset (input.offset+input.len) positive fits hidden
    (by obtain ⟨node,present,tag,parent,children,permission,exposed⟩:=metadata.newNode;have same:=Option.some.inj (context.anchorPresent.symm.trans present);rw [same];exact children)
    metadata.freshLookup active owned
  have releasedGeometry := GeneralBorrowStructuralReleaseGeometry.release child protections input.newTag geometry.1
  exact ⟨done.1,done.2.1,done.2.2,releasedGeometry.1,releasedGeometry.2.trans geometry.2⟩
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedRelease
