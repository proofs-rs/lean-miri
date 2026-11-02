import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedData
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableCleanReadRange
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedRelease
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedRun
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadRange
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedReadRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedInactiveWritableSharedConstructor (ResourcesFor)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem release {profileMode : ProfileMode} (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : ResourcesFor input protections selected head tail writable profileMode)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index input)=none) input.tree.locations) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected
    let released := child.tree.releaseProtector input.newTag protections
    released.status=.Released ∧
      GeneralRangeMapOrigins.OwnedOn (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data released.tree location protections
        (index input) selected head tail (fun position => raw.component.support position ∨ position=(index input).toNat)
        (GeneralBorrowFreshMixedChild.extend writable (index input).toNat)))
        input.offset (input.offset+input.len) released.tree.locations ∧
      released.tree.locations.WellFormed ∧ released.tree.locations.size=input.tree.locations.size := by
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedInactiveWritableSharedRun.prepare_mode input protections selected head tail writable raw
  obtain ⟨context,owned⟩ := GeneralBorrowExposedScopedInactiveWritableSharedData.build input protections selected head tail writable raw
  have fits : input.tree.nodes.data.size≤4294967296 := by have a:=input.aligned;have b:=input.fits;omega
  have vacant : input.tree.nodes.get (index input)=none := by
    unfold UniValMap.get
    have endIndex : (index input).toNat=input.tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end input
    rw [endIndex]
    simp
  have preserved := GeneralBorrowExposedScopedInactiveWritableCleanReadRange.ranged input.tree protections input.parentTag input.parent selected head (index input) tail
    (Size.ofBytes input.offset) (Size.ofBytes input.len) context raw.component.support writable fits input.parentTagPresent vacant clean
    input.well input.offset (input.offset+input.len) owned input.bounds (Nat.le_refl _) (Nat.le_refl _)
  have preparedClean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index prepared)=none) prepared.tree.locations := by
    rw [indexEq,treeEq]
    exact preserved.2
  have released := GeneralBorrowExposedScopedInactiveWritableSharedRelease.release prepared protections selected head tail writable preparedRaw
    (by rw [offsetEq,lenEq];exact positive) preparedClean
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have childEq : result prepared =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected).tree := by
    simp only [result,treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq]
  rw [childEq,newTagEq] at released
  refine ⟨released.1,?_,released.2.2.2.1,?_⟩
  · simpa only [indexEq,offsetEq,lenEq,supportEq] using released.2.2.1
  · have good := GeneralBorrowExposedScopedInactiveWritableReadRange.access input.tree protections input.parentTag input.parent selected head tail
      (Size.ofBytes input.offset) (Size.ofBytes input.len) context raw.component.support writable fits input.parentTagPresent input.well
      input.offset (input.offset+input.len) owned input.bounds (Nat.le_refl _) (Nat.le_refl _)
    exact released.2.2.2.2.trans (by rw [treeEq];exact good.2.2.2)
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedReadRelease
