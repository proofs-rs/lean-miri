import duplicate_prefix.GeneralBorrowExposedScopedDefaultLeafExpressionData
import duplicate_prefix.GeneralBorrowExposedScopedProtectedMutableLeafPipeline
import duplicate_prefix.GeneralBorrowExposedScopedCleanReadRange
import duplicate_prefix.GeneralBorrowExposedScopedProtectedMutableReleaseReady
namespace DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableReadReleaseReady
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildDefault
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedDefaultLeafConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem ready (input : Input) (global : GlobalState) (allocation : AllocId) (selected head : UniIndex) (tail : List UniIndex)
    (raw : Resources input global.protectedTags selected head tail)
    (nodeTags : ∀ index node,input.tree.nodeAt index=some node → input.tree.indexOfTag node.tag=some index)
    (atBase : input.offset=0) (full : input.len=input.tree.locations.size.bytes)
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
          Nonempty (GeneralBorrowExposedScopedUniqueReadData.Data released.tree location (global.endCall frame).protectedTags
            (index input) selected head tail (fun position => raw.component.support position ∨ position=(index input).toNat) (fun _=>true)) ∧
          Nonempty (GeneralBorrowExposedKnownRootRangeData.Data released.tree location (global.endCall frame).protectedTags
            (index input) selected head tail .Write)) input.offset (input.offset+input.len) released.tree.locations ∧
        released.tree.locations.WellFormed ∧ released.tree.locations.size=input.tree.locations.size := by
  let protections := global.protectedTags
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedDefaultLeafRun.prepare input protections selected head tail raw atBase full .VisitChildrenOfAccessed
  obtain ⟨context,mixedOwned⟩ := GeneralBorrowExposedScopedDefaultLeafExpressionData.build input protections selected head tail raw
  have owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowExposedScopedUniqueReadData.Data input.tree location protections
        input.parent selected head tail raw.component.support (fun _=>true))) input.offset (input.offset+input.len) input.tree.locations := by
    intro position valid positive lower upper
    obtain ⟨data⟩ := mixedOwned position valid positive lower upper
    exact ⟨⟨data,(by have room:=raw.room;omega),raw.leaves,fun query included => raw.unique query included position valid⟩⟩
  have fits : input.tree.nodes.data.size≤4294967296 := by have a:=input.aligned;have b:=input.fits;omega
  have vacant : input.tree.nodes.get (index input)=none := by
    unfold UniValMap.get
    have endIndex : (index input).toNat=input.tree.nodes.data.size := GeneralBorrowFreshMetadataChildDefault.at_end input
    rw [endIndex]
    simp
  have preserved := GeneralBorrowExposedScopedCleanReadRange.ranged input.tree protections input.parentTag input.parent selected head (index input) tail
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed context raw.component.support (fun _=>true) fits input.parentTagPresent vacant clean
    input.well input.offset (input.offset+input.len) owned input.bounds (Nat.le_refl _) (Nat.le_refl _)
  have preparedClean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutable.index (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared))=none) prepared.tree.locations := by
    change GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index prepared)=none) prepared.tree.locations
    rw [indexEq,treeEq]
    exact preserved.2
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have tagsPrepared : ∀ query node,prepared.tree.nodeAt query=some node → prepared.tree.indexOfTag node.tag=some query := by
    intro query node present
    rw [treeEq,frame] at present ⊢
    exact nodeTags query node present
  have released := GeneralBorrowExposedScopedProtectedMutableReleaseReady.ready
    (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared) global allocation selected head tail
    (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableResources prepared protections selected head tail preparedRaw)
    tagsPrepared (by simpa only [GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput,offsetEq,lenEq] using positive) preparedClean
  have childEq : GeneralBorrowFreshMetadataChildMutable.result (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared) =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read global.protectedTags .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree := by
    simp only [GeneralBorrowFreshMetadataChildMutable.result,GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput,treeEq,parentTagEq,newTagEq,offsetEq,lenEq,protections]
  have newTagMutable : (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared).newTag = input.newTag := newTagEq
  rw [childEq,newTagMutable] at released
  obtain ⟨nextContext,nextOwned,well,capacity⟩ := released.2
  have indexMutable : GeneralBorrowFreshMetadataChildMutable.index (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared) = index input := indexEq
  have supportMutable : (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableResources prepared protections selected head tail preparedRaw).component.support = raw.component.support := supportEq
  have offsetMutable : (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared).offset = input.offset := offsetEq
  have lenMutable : (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared).len = input.len := lenEq
  rw [indexMutable] at nextContext
  simp only [indexMutable,supportMutable,offsetMutable,lenMutable] at nextOwned
  have good := GeneralBorrowExposedScopedUniqueReadRange.access input.tree protections input.parentTag input.parent selected head tail
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed context raw.component.support (fun _=>true) fits input.parentTagPresent input.well
    input.offset (input.offset+input.len) owned input.bounds (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨released.1,nextContext,nextOwned,well,capacity.trans (by change prepared.tree.locations.size = input.tree.locations.size;rw [treeEq];exact good.2.2.2)⟩
end DuplicatePrefix.GeneralBorrowExposedScopedProtectedMutableReadReleaseReady
