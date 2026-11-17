import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedTargetActivity
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableCleanReadRange
import duplicate_prefix.GeneralBorrowExposedScopedSharedActivity
import duplicate_prefix.GeneralBorrowActiveWithinRelease
namespace DuplicatePrefix.GeneralBorrowScopedConcreteLenTargetActivity
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildShared GeneralBorrowFreshActiveWithin GeneralBorrowExposedScopedSharedPathMetadata
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
/-- Actual shared parent Read, constructor and confined helper release preserve
an older target's window activity, including exposed selected components. -/
theorem source {profileMode : ProfileMode} (input : Input) (tags : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat→Bool)
    (raw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor input tags selected head tail writable profileMode)
    (target : UniIndex) (offset len : UInt64) (tag : BorTag)
    (offsetAlias : input.offset=offset) (lenAlias : input.len=len) (tagEq : input.newTag=tag)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (index input)=none) input.tree.locations)
    (initial : ActiveWithin input.tree target .Write offset (offset+len)) :
    ActiveWithin ((child input tags .VisitChildrenOfAccessed).releaseProtector tag tags).tree target .Write offset (offset+len) := by
  have second := GeneralBorrowExposedScopedInactiveWritableSharedTargetActivity.preserve input tags selected head tail writable raw
    target offset (offset+len) (by simpa only [offsetAlias] using (Nat.le_refl offset.toNat))
    (by simpa only [offsetAlias,lenAlias] using (Nat.le_refl (offset+len).toNat)) initial
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedInactiveWritableSharedRun.prepare_mode input tags selected head tail writable raw
  obtain ⟨context,owned⟩:=GeneralBorrowExposedScopedInactiveWritableSharedData.build input tags selected head tail writable raw
  have vacant : input.tree.nodes.get (index input)=none := by
    unfold UniValMap.get
    rw [at_end input]
    simp
  have nodeFits : input.tree.nodes.data.size≤4294967296 := by have bound:=input.fits;have aligned:=input.aligned;omega
  have readClean := GeneralBorrowExposedScopedInactiveWritableCleanReadRange.ranged input.tree tags input.parentTag input.parent selected head (index input)
    tail (Size.ofBytes input.offset) (Size.ofBytes input.len) context raw.component.support writable nodeFits
    input.parentTagPresent vacant clean input.well input.offset (input.offset+input.len) owned input.bounds (Nat.le_refl _) (Nat.le_refl _)
  have preparedClean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (index prepared)=none) prepared.tree.locations := by
    rw [indexEq,treeEq]
    exact readClean.2
  have helperRead := GeneralBorrowExposedScopedSharedActivity.append prepared.tree prepared.depth prepared.parentTag prepared.newTag prepared.parent prepared.parentNode
    prepared.parentTagPresent prepared.parentPresent prepared.fresh prepared.noFree prepared.aligned prepared.fits prepared.isProtected prepared.offset prepared.len
    prepared.nonzero prepared.well prepared.bounds preparedClean
  have childEq : result prepared=child input tags .VisitChildrenOfAccessed := by
    simp only [result,child,treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq]
  have helper : ActiveWithin (child input tags .VisitChildrenOfAccessed) (index input) .Write offset (offset+len) := by
    have broad := to_write _ _ _ _ helperRead
    change ActiveWithin (result prepared) (index prepared) .Write prepared.offset (prepared.offset+prepared.len) at broad
    rw [childEq,indexEq,offsetEq,lenEq,offsetAlias,lenAlias] at broad
    exact broad
  let metadata := append prepared
  obtain ⟨node,present,nodeTag,parent,children,permission,hidden⟩:=metadata.newNode
  have helperPresent : (child input tags .VisitChildrenOfAccessed).nodeAt (index input)=some node := by rw [←childEq,←indexEq];exact present
  have helperTag : (child input tags .VisitChildrenOfAccessed).indexOfTag tag=some (index input) := by
    rw [←childEq,←indexEq,←tagEq,←newTagEq]
    exact metadata.freshLookup
  have released := GeneralBorrowActiveWithinRelease.release (child input tags .VisitChildrenOfAccessed) tags tag
    (index input) target node helperTag helperPresent hidden offset (offset+len) helper second

  exact released
end
end DuplicatePrefix.GeneralBorrowScopedConcreteLenTargetActivity
