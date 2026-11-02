import duplicate_prefix.GeneralBorrowExposedScopedAncestorSharedMixedConstructor
import duplicate_prefix.GeneralBorrowExposedScopedAncestorMixedRelease
import duplicate_prefix.GeneralBorrowExposedScopedSharedActivity
import duplicate_prefix.GeneralBorrowFreshSharedGeometry
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometry
namespace DuplicatePrefix.GeneralBorrowExposedScopedAncestorSharedMixedRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedAncestorSharedConstructor (Resources)
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
      GeneralBorrowExposedConstructorAncestry.OnPath released.tree (index input) support ∧
      GeneralRangeMapOrigins.OwnedOn (fun location => GeneralBorrowExposedScopedAncestorMixedRangeData.Post released.tree location protections
        (index input) support (GeneralBorrowFreshMixedChild.extend writable (index input).toNat)) input.offset (input.offset+input.len) released.tree.locations ∧
      released.tree.locations.WellFormed ∧ released.tree.locations.size=input.tree.locations.size := by
  let child := result input
  let metadata := append input
  let support := fun position => raw.component.support position ∨ position=(index input).toNat
  obtain ⟨success,context,owned⟩ := GeneralBorrowExposedScopedAncestorSharedMixedConstructor.construct input protections selected head tail writable raw
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
  have done := GeneralBorrowExposedScopedAncestorMixedRelease.release child protections input.newTag (index input) selected head tail context
    support (GeneralBorrowFreshMixedChild.extend writable (index input).toNat) input.offset (input.offset+input.len) positive fits (nodeEq ▸ hidden) (nodeEq ▸ leaf) metadata.freshLookup active owned
  have ancestry := GeneralBorrowExposedConstructorAncestry.release child protections input.newTag (index input)
    (GeneralBorrowExposedConstructorAncestry.extended raw.component.support (index input))
    (GeneralBorrowExposedConstructorAncestry.shared input raw.component.support raw.forest raw.ancestry)
  have finalAncestry : GeneralBorrowExposedConstructorAncestry.OnPath (child.releaseProtector input.newTag protections).tree (index input) support := by
    intro query old member found exposed
    exact ancestry query old (member.elim Or.inr Or.inl) found exposed
  have releasedGeometry := GeneralBorrowStructuralReleaseGeometry.release child protections input.newTag geometry.1
  exact ⟨done.1,done.2.1,finalAncestry,done.2.2,releasedGeometry.1,releasedGeometry.2.trans geometry.2⟩
end DuplicatePrefix.GeneralBorrowExposedScopedAncestorSharedMixedRelease
