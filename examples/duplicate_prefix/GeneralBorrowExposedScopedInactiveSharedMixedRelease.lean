import duplicate_prefix.GeneralBorrowExposedScopedInactiveSharedMixedConstructor
import duplicate_prefix.GeneralBorrowExposedScopedInactiveMixedRelease
import duplicate_prefix.GeneralBorrowExposedScopedInactiveRelease
import duplicate_prefix.GeneralBorrowExposedScopedSharedActivity
import duplicate_prefix.GeneralBorrowFreshSharedGeometry
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometry
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveSharedMixedRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedInactiveSharedConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Real shared child construction and actual release retain exposed selected
ancestors and their Unique permissions. Only the fresh helper is a hidden leaf;
initial allocator-slot cleanliness supplies its actual active-range profile. -/
theorem release (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index input)=none) input.tree.locations) :
    let child := result input
    let released := child.releaseProtector input.newTag protections
    let support := fun position => raw.component.support position ∨ position=(index input).toNat
    released.status=.Released ∧ released.tree={child with locations:=released.tree.locations} ∧
      GeneralRangeMapState.Every (fun location => GeneralBorrowExposedInactiveConstructor.Profile released.tree location (index input) support) released.tree.locations ∧
      GeneralRangeMapOrigins.OwnedOn (fun location => GeneralBorrowExposedScopedInactiveMixedRangeData.Post released.tree location protections
        (index input) support (GeneralBorrowFreshMixedChild.extend writable (index input).toNat)) input.offset (input.offset+input.len) released.tree.locations ∧
      released.tree.locations.WellFormed ∧ released.tree.locations.size=input.tree.locations.size := by
  let child := result input
  let metadata := append input
  let support := fun position => raw.component.support position ∨ position=(index input).toNat
  obtain ⟨success,context,owned⟩ := GeneralBorrowExposedScopedInactiveSharedMixedConstructor.construct input protections selected head tail writable raw
  have geometry := GeneralBorrowFreshSharedGeometry.append_frame input
  have activity := GeneralBorrowExposedScopedSharedActivity.append input.tree input.depth input.parentTag input.newTag input.parent input.parentNode
    input.parentTagPresent input.parentPresent input.fresh input.noFree input.aligned input.fits input.isProtected input.offset input.len
    input.nonzero input.well input.bounds clean
  have active := GeneralBorrowFreshActiveWithin.active_on child (index input) .Read input.offset (input.offset+input.len) geometry.1 activity
  have fits : child.nodes.data.size≤4294967296 := by
    change child.nodes.size≤4294967296
    rw [metadata.size]
    have bound:=raw.room
    omega
  obtain ⟨node,present,_,_,leaf,_,hidden⟩ := metadata.newNode
  have nodeEq : context.anchorNode=node := Option.some.inj (context.anchorPresent.symm.trans present)
  have done := GeneralBorrowExposedScopedInactiveMixedRelease.release child protections input.newTag (index input) selected head tail context
    support (GeneralBorrowFreshMixedChild.extend writable (index input).toNat) input.offset (input.offset+input.len) positive fits (nodeEq ▸ hidden) (nodeEq ▸ leaf) metadata.freshLookup active owned
  have initialExposures := GeneralBorrowExposedInactiveConstructor.shared input raw.component.support raw.forest raw.exposures
  have initialProfile : GeneralRangeMapState.Every (fun location => GeneralBorrowExposedInactiveConstructor.Profile child location (index input) support) child.locations := by
    intro position valid query value member found exposed
    exact initialExposures position valid query value (member.elim Or.inr Or.inl) found exposed
  have baseOwned : GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedInactiveRangeData.Data child location protections
      (index input) selected head tail support)) input.offset (input.offset+input.len) child.locations := by
    intro position valid positive low high
    obtain ⟨data⟩ := owned position valid positive low high
    exact ⟨data.base⟩
  have baseDone := GeneralBorrowExposedScopedInactiveRelease.release child protections input.newTag (index input) selected head tail context support
    input.offset (input.offset+input.len) positive fits (nodeEq ▸ hidden) (nodeEq ▸ leaf) metadata.freshLookup active baseOwned initialProfile
  have releasedGeometry := GeneralBorrowStructuralReleaseGeometry.release child protections input.newTag geometry.1
  exact ⟨done.1,done.2.1,baseDone.2.2,done.2.2,releasedGeometry.1,releasedGeometry.2.trans geometry.2⟩
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveSharedMixedRelease
