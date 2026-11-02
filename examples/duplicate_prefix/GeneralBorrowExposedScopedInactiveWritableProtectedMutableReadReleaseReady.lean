import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableData
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableRun
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableCleanReadRange
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableReleaseReady
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableReadReleaseReady
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildMutable
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedInactiveWritableProtectedMutableConstructor (ResourcesFor)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem ready {profileMode : ProfileMode} (input : Input) (global : GlobalState) (allocation : AllocId) (selected head : UniIndex) (tail : List UniIndex)
    (raw : ResourcesFor input global.protectedTags selected head tail profileMode)
    (nodeTags : ∀ index node,input.tree.nodeAt index=some node → input.tree.indexOfTag node.tag=some index)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index input)=none) input.tree.locations) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read global.protectedTags .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    let released := child.tree.releaseProtector input.newTag global.protectedTags
    let frame := ({} : FrameState).addProtector allocation input.newTag
    released.status=.Released ∧
      ∃ context : GeneralBorrowExposedKnownRootRangeData.Context released.tree (index input) selected head tail,
        GeneralRangeMapOrigins.OwnedOn (fun location =>
          Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data released.tree location (global.endCall frame).protectedTags
            (index input) selected head tail (fun position => raw.component.support position ∨ position=(index input).toNat) (fun _=>true))) input.offset (input.offset+input.len) released.tree.locations ∧
        released.tree.locations.WellFormed ∧ released.tree.locations.size=input.tree.locations.size := by
  let protections := global.protectedTags
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
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have tagsPrepared : ∀ query node,prepared.tree.nodeAt query=some node → prepared.tree.indexOfTag node.tag=some query := by
    intro query node present
    rw [treeEq,frame] at present ⊢
    exact nodeTags query node present
  have released := GeneralBorrowExposedScopedInactiveWritableProtectedMutableReleaseReady.ready
    prepared global allocation selected head tail
    preparedRaw
    tagsPrepared (by simpa only [offsetEq,lenEq] using positive) preparedClean
  have childEq : GeneralBorrowFreshMetadataChildMutable.result prepared =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read global.protectedTags .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree := by
    simp only [GeneralBorrowFreshMetadataChildMutable.result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq,protections]
  have newTagMutable : prepared.newTag = input.newTag := newTagEq
  rw [childEq,newTagMutable] at released
  obtain ⟨nextContext,nextOwned,well,capacity⟩ := released.2
  have indexMutable : GeneralBorrowFreshMetadataChildMutable.index prepared = index input := indexEq
  have supportMutable : preparedRaw.component.support = raw.component.support := supportEq
  have offsetMutable : prepared.offset = input.offset := offsetEq
  have lenMutable : prepared.len = input.len := lenEq
  rw [indexMutable] at nextContext
  simp only [indexMutable,supportMutable,offsetMutable,lenMutable] at nextOwned
  have good := GeneralBorrowExposedScopedInactiveWritableReadRange.access input.tree protections input.parentTag input.parent selected head tail
    (Size.ofBytes input.offset) (Size.ofBytes input.len) context raw.component.support (fun _=>true) fits input.parentTagPresent input.well
    input.offset (input.offset+input.len) owned input.bounds (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨released.1,nextContext,nextOwned,well,capacity.trans (by change prepared.tree.locations.size = input.tree.locations.size;rw [treeEq];exact good.2.2.2)⟩
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableReadReleaseReady
