import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableData
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableRun
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableCleanReadRange
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableAsMutConstructorReleaseData
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAsMutEntryReleaseData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildMutable
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedInactiveWritableProtectedMutableConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def build {profileMode : ProfileMode} (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedInactiveWritableProtectedMutableConstructor.ResourcesFor input protections selected head tail profileMode)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index input)=none) input.tree.locations) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    GeneralBorrowExposedScopedInactiveWritableAsMutReleasePlan.Input child.tree protections input.newTag := by
  apply Classical.choice
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedInactiveWritableProtectedMutableRun.prepare_mode input protections selected head tail raw
  obtain ⟨context,owned⟩ := GeneralBorrowExposedScopedInactiveWritableProtectedMutableData.build input protections selected head tail raw
  have fits : input.tree.nodes.data.size≤4294967296 := by have a:=input.aligned;have b:=input.fits;omega
  have vacant : input.tree.nodes.get (index input)=none := by
    unfold UniValMap.get
    have endIndex : (index input).toNat=input.tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
    rw [endIndex]
    simp
  have preserved := GeneralBorrowExposedScopedInactiveWritableCleanReadRange.ranged input.tree protections input.parentTag input.parent selected head (index input) tail
    (Size.ofBytes input.offset) (Size.ofBytes input.len) context raw.component.support (fun _=>true) fits input.parentTagPresent vacant clean
    input.well input.offset (input.offset+input.len) owned input.bounds (Nat.le_refl _) (Nat.le_refl _)
  have preparedClean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutable.index prepared)=none) prepared.tree.locations := by
    change GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index prepared)=none) prepared.tree.locations
    rw [indexEq,treeEq]
    exact preserved.2
  have result := GeneralBorrowExposedScopedInactiveWritableAsMutConstructorReleaseData.build
    prepared protections selected head tail
    preparedRaw
    (by simpa only [offsetEq,lenEq] using positive) preparedClean
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have childEq : GeneralBorrowFreshMetadataChildMutable.result prepared =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree := by
    simp only [GeneralBorrowFreshMetadataChildMutable.result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  have newTagMutable : prepared.newTag = input.newTag := newTagEq
  rw [childEq,newTagMutable] at result
  exact ⟨result⟩
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAsMutEntryReleaseData
