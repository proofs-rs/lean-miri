import duplicate_prefix.GeneralBorrowExposedScopedAncestorSharedProtectFresh
import duplicate_prefix.GeneralBorrowExposedScopedAncestorSharedMixedRelease
namespace DuplicatePrefix.GeneralBorrowExposedScopedAncestorStrongSharedEpisode
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedScopedAncestorSharedConstructor (Resources)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The real fresh Strong registration supplies protected constructor/release
resources internally. Exposed selected ancestors retain their source path and
Unique permissions; mixed labels and exact cache coherence survive release.
This is a source BorrowTree episode, not a whole-function/global history claim. -/
theorem run (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (nodeTags : GeneralBorrowGcAllocator.NodeTags input.tree) (held : input.isProtected=true)
    (positive : input.offset.toNat<(input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index input)=none) input.tree.locations) :
    let registered := protections.insert input.newTag .StrongProtector
    let child := result input
    let released := child.releaseProtector input.newTag registered
    let support := fun position => raw.component.support position ∨ position=(index input).toNat
    (input.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen true).outcome=.ok () ∧
    released.status=.Released ∧ released.tree={child with locations:=released.tree.locations} ∧
    GeneralBorrowExposedConstructorAncestry.OnPath released.tree (index input) support ∧
    GeneralRangeMapOrigins.OwnedOn (fun location => GeneralBorrowExposedScopedAncestorMixedRangeData.Post released.tree location registered
      (index input) support (GeneralBorrowFreshMixedChild.extend writable (index input).toNat)) input.offset (input.offset+input.len) released.tree.locations ∧
    released.tree.locations.WellFormed ∧ released.tree.locations.size=input.tree.locations.size := by
  obtain ⟨registeredRaw,supportEq⟩ := GeneralBorrowExposedScopedAncestorSharedProtectFresh.protect input protections selected head tail writable raw nodeTags
  have formed := GeneralBorrowExposedScopedAncestorSharedMixedConstructor.construct input (protections.insert input.newTag .StrongProtector)
    selected head tail writable registeredRaw
  have done := GeneralBorrowExposedScopedAncestorSharedMixedRelease.release input (protections.insert input.newTag .StrongProtector)
    selected head tail writable registeredRaw positive clean
  refine ⟨?_,?_⟩
  · simpa only [held] using formed.1
  · simpa only [supportEq] using done
end DuplicatePrefix.GeneralBorrowExposedScopedAncestorStrongSharedEpisode
