import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableDefaultRun
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableRun
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableData
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableCleanReadRange
import duplicate_prefix.GeneralBorrowFreshDefaultTargetWithin
import duplicate_prefix.GeneralBorrowFreshMutableTargetWithin
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
import duplicate_prefix.GeneralBorrowExposedScopedWindowReleaseActivity
import duplicate_prefix.GeneralBorrowActiveWithinRelease
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableTargetActivity
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshActiveWithin
variable [area : GeneralBorrowExposedKnownRootState.Scope]
variable {profileMode : ProfileMode}
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

def defaultChild (input : GeneralBorrowFreshMetadataChildDefault.Input) (protections : ProtectedTags) :=
  let read:=input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  (read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
    (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree

def mutableChild (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags) :=
  let read:=input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  (read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
    (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree

theorem default_target (input : GeneralBorrowFreshMetadataChildDefault.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedInactiveWritableDefaultConstructor.ResourcesFor input protections selected head tail profileMode)
    (target : UniIndex) (lower upper : UInt64)
    (requestLower : lower.toNat≤input.offset.toNat) (requestUpper : (input.offset+input.len).toNat≤upper.toNat)
    (active : ActiveWithin input.tree target .Write lower upper) :
    ActiveWithin (defaultChild input protections) target .Write lower upper := by
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩:=
    GeneralBorrowExposedScopedInactiveWritableDefaultRun.prepare_mode input protections selected head tail raw
  have readActive:=GeneralBorrowFreshActiveWithinAccess.normal input.tree input.parentTag (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read protections .VisitChildrenOfAccessed target lower upper input.well input.bounds requestLower requestUpper active
  have preparedActive : ActiveWithin prepared.tree target .Write lower upper := by rw [treeEq];exact readActive
  have kept:=GeneralBorrowFreshDefaultTargetWithin.append prepared.tree prepared.parentTag prepared.newTag prepared.parent prepared.parentNode
    prepared.parentTagPresent prepared.parentPresent prepared.fresh prepared.noFree prepared.aligned prepared.fits
    prepared.offset prepared.len prepared.nonzero prepared.well prepared.bounds target lower upper
    (by rw [offsetEq];exact requestLower) (by rw [offsetEq,lenEq];exact requestUpper) preparedActive
  simpa only [defaultChild,treeEq,parentTagEq,newTagEq,offsetEq,lenEq] using kept

/-- Source-formed helper inactivity confines every actual release callback, so
an older target retains its strong window activity through the whole real
parent-Read/protected-constructor/release sequence, even on release failure. -/
theorem mutable_release_target (input : GeneralBorrowFreshMetadataChildMutable.Input) (protections : ProtectedTags)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedInactiveWritableProtectedMutableConstructor.ResourcesFor input protections selected head tail profileMode)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (GeneralBorrowFreshMetadataChildMutable.index input)=none) input.tree.locations)
    (target : UniIndex)
    (active : ActiveWithin input.tree target .Write input.offset (input.offset+input.len)) :
    ActiveWithin ((mutableChild input protections).releaseProtector input.newTag protections).tree
      target .Write input.offset (input.offset+input.len) := by
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩:=
    GeneralBorrowExposedScopedInactiveWritableProtectedMutableRun.prepare_mode input protections selected head tail raw
  have readActive:=GeneralBorrowFreshActiveWithinAccess.normal input.tree input.parentTag (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read protections .VisitChildrenOfAccessed target input.offset (input.offset+input.len) input.well input.bounds (Nat.le_refl _) (Nat.le_refl _) active
  have preparedActive : ActiveWithin prepared.tree target .Write prepared.offset (prepared.offset+prepared.len) := by
    rw [treeEq,offsetEq,lenEq];exact readActive
  have targetActive:=GeneralBorrowFreshMutableTargetWithin.append prepared.tree prepared.parentTag prepared.newTag prepared.parent prepared.parentNode
    prepared.parentTagPresent prepared.parentPresent prepared.fresh prepared.noFree prepared.aligned prepared.fits
    prepared.offset prepared.len prepared.nonzero prepared.well prepared.bounds target prepared.offset (prepared.offset+prepared.len)
    (Nat.le_refl _) (Nat.le_refl _) preparedActive
  obtain ⟨context,owned⟩:=GeneralBorrowExposedScopedInactiveWritableProtectedMutableData.build input protections selected head tail raw
  have fits : input.tree.nodes.data.size≤4294967296 := by have a:=input.aligned;have b:=input.fits;omega
  have vacant : input.tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input)=none := by
    unfold UniValMap.get
    rw [GeneralBorrowFreshMetadataChildMutable.at_end input]
    simp
  have preserved:=GeneralBorrowExposedScopedInactiveWritableCleanReadRange.ranged input.tree protections input.parentTag input.parent selected head
    (GeneralBorrowFreshMetadataChildMutable.index input) tail (Size.ofBytes input.offset) (Size.ofBytes input.len)
    context raw.component.support (fun _=>true) fits input.parentTagPresent vacant clean input.well input.offset (input.offset+input.len) owned
    input.bounds (Nat.le_refl _) (Nat.le_refl _)
  have preparedClean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (GeneralBorrowFreshMetadataChildMutable.index prepared)=none) prepared.tree.locations := by
    rw [indexEq,treeEq];exact preserved.2
  let metadata:=GeneralBorrowFreshMetadataChildMutable.append prepared
  obtain ⟨node,present,tag,parent,children,permission,hidden⟩:=metadata.newNode
  have helperActive:=GeneralBorrowExposedScopedWindowReleaseActivity.mutable prepared preparedClean
  have actual:=GeneralBorrowActiveWithinRelease.release (GeneralBorrowFreshMetadataChildMutable.result prepared) protections prepared.newTag
    (GeneralBorrowFreshMetadataChildMutable.index prepared) target node metadata.freshLookup present hidden prepared.offset (prepared.offset+prepared.len)
    (GeneralBorrowFreshActiveWithin.to_write _ _ _ _ helperActive) targetActive
  simpa only [GeneralBorrowFreshMetadataChildMutable.result,mutableChild,treeEq,parentTagEq,newTagEq,offsetEq,lenEq] using actual
end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableTargetActivity
