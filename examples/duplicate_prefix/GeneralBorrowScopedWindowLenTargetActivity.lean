import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableLenCallInput
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableSharedTargetActivity
import duplicate_prefix.GeneralBorrowExposedScopedWritableCleanReadRange
import duplicate_prefix.GeneralBorrowExposedScopedSharedActivity
import duplicate_prefix.GeneralBorrowActiveWithinRelease
namespace DuplicatePrefix.GeneralBorrowScopedWindowLenTargetActivity
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildShared GeneralBorrowFreshActiveWithin GeneralBorrowExposedScopedSharedPathMetadata
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
def held (s : GeneralBorrowExposedScopedWindowWritableLenCallInput.Input) :=
  TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh) s.tracker.global.nextPointerTag

/-- Both actual shared Reads/constructors and the helper's confined actual
release preserve the source target's outside inactivity. No successful access
or final target activity is an input. Window aliases come from the real prefix. -/
theorem source (s : GeneralBorrowExposedScopedWindowWritableLenCallInput.Input)
    (firstOffset : s.first.offset=s.offset) (firstLen : s.first.len=s.len)
    (initial : ActiveWithin s.first.tree s.first.parent .Write s.offset (s.offset+s.len)) :
    let tags := (held s).global.protectedTags
    ActiveWithin ((GeneralBorrowExposedScopedSharedArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.exprTag s.offset s.len).releaseProtector
      s.tracker.global.nextPointerTag tags).tree s.first.parent .Write s.offset (s.offset+s.len) := by
  let tags := (held s).global.protectedTags
  have first := GeneralBorrowExposedScopedWindowWritableSharedTargetActivity.preserve s.first s.firstTags s.selected s.head s.tail (fun _=>true)
    s.firstRaw s.first.parent s.offset (s.offset+s.len) (by simpa only [firstOffset] using (Nat.le_refl s.offset.toNat)) (by simpa only [firstOffset,firstLen] using (Nat.le_refl (s.offset+s.len).toNat)) initial
  have middle : ActiveWithin s.input.tree s.first.parent .Write s.offset (s.offset+s.len) := by rw [s.firstTreeEq];exact first
  have second := GeneralBorrowExposedScopedWindowWritableSharedTargetActivity.preserve s.input tags s.selected s.head s.tail s.writable s.raw
    s.first.parent s.offset (s.offset+s.len) (by simpa only [s.offsetEq] using (Nat.le_refl s.offset.toNat)) (by simpa only [s.offsetEq,s.lenEq] using (Nat.le_refl (s.offset+s.len).toNat)) middle
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedWindowWritableSharedRun.prepare s.input tags s.selected s.head s.tail s.writable s.raw .VisitChildrenOfAccessed
  obtain ⟨context,owned⟩:=GeneralBorrowExposedScopedWritableSharedData.build s.input tags s.selected s.head s.tail s.writable s.raw
  have vacant : s.input.tree.nodes.get (index s.input)=none := by
    unfold UniValMap.get
    rw [at_end s.input]
    simp
  have nodeFits : s.input.tree.nodes.data.size≤4294967296 := by have bound:=s.input.fits;have aligned:=s.input.aligned;omega
  have readClean := GeneralBorrowExposedScopedWritableCleanReadRange.ranged s.input.tree tags s.input.parentTag s.input.parent s.selected s.head (index s.input)
    s.tail (Size.ofBytes s.input.offset) (Size.ofBytes s.input.len) .VisitChildrenOfAccessed context s.raw.component.support s.writable nodeFits
    s.input.parentTagPresent vacant s.clean s.input.well s.input.offset (s.input.offset+s.input.len) owned s.input.bounds (Nat.le_refl _) (Nat.le_refl _)
  have preparedClean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (index prepared)=none) prepared.tree.locations := by
    rw [indexEq,treeEq]
    exact readClean.2
  have helperRead := GeneralBorrowExposedScopedSharedActivity.append prepared.tree prepared.depth prepared.parentTag prepared.newTag prepared.parent prepared.parentNode
    prepared.parentTagPresent prepared.parentPresent prepared.fresh prepared.noFree prepared.aligned prepared.fits prepared.isProtected prepared.offset prepared.len
    prepared.nonzero prepared.well prepared.bounds preparedClean
  have childEq : result prepared=child s.input tags .VisitChildrenOfAccessed := by
    simp only [result,child,treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq]
  have helper : ActiveWithin (child s.input tags .VisitChildrenOfAccessed) (index s.input) .Write s.offset (s.offset+s.len) := by
    have broad := to_write _ _ _ _ helperRead
    change ActiveWithin (result prepared) (index prepared) .Write prepared.offset (prepared.offset+prepared.len) at broad
    rw [childEq,indexEq,offsetEq,lenEq,s.offsetEq,s.lenEq] at broad
    exact broad
  let metadata := append prepared
  obtain ⟨node,present,tag,parent,children,permission,hidden⟩:=metadata.newNode
  have helperPresent : (child s.input tags .VisitChildrenOfAccessed).nodeAt (index s.input)=some node := by rw [←childEq,←indexEq];exact present
  have helperTag : (child s.input tags .VisitChildrenOfAccessed).indexOfTag s.tracker.global.nextPointerTag=some (index s.input) := by
    rw [←childEq,←indexEq,←s.tagEq,←newTagEq]
    exact metadata.freshLookup
  have released := GeneralBorrowActiveWithinRelease.release (child s.input tags .VisitChildrenOfAccessed) tags s.tracker.global.nextPointerTag
    (index s.input) s.first.parent node helperTag helperPresent hidden s.offset (s.offset+s.len) helper second
  have actual : child s.input tags .VisitChildrenOfAccessed=GeneralBorrowExposedScopedSharedArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.exprTag s.offset s.len := by
    simp only [child,GeneralBorrowExposedScopedSharedArgumentCopy.finalTree,s.treeEq,s.parentTagEq,s.tagEq,s.offsetEq,s.lenEq,s.protectedEq]
    rfl
  rw [actual] at released
  exact released
end
end DuplicatePrefix.GeneralBorrowScopedWindowLenTargetActivity
