import duplicate_prefix.GeneralBorrowExposedScopedDefaultLeafExpressionData
import duplicate_prefix.GeneralBorrowExposedScopedProtectedMutableLeafPipeline
import duplicate_prefix.GeneralBorrowExposedScopedCleanReadRange
import duplicate_prefix.GeneralBorrowExposedScopedAsMutConstructorReleaseData
namespace DuplicatePrefix.GeneralBorrowExposedScopedAsMutEntryReleaseData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildDefault
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedDefaultLeafConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

noncomputable def build (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : Resources input protections selected head tail)
    (atBase : input.offset=0) (full : input.len=input.tree.locations.size.bytes)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index input)=none) input.tree.locations) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    GeneralBorrowExposedScopedAsMutReleasePlan.Input child.tree protections input.newTag := by
  apply Classical.choice
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
  have result := GeneralBorrowExposedScopedAsMutConstructorReleaseData.build
    (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared) protections selected head tail
    (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableResources prepared protections selected head tail preparedRaw)
    (by simpa only [GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput,offsetEq,lenEq] using positive) preparedClean
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have childEq : GeneralBorrowFreshMetadataChildMutable.result (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared) =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree := by
    simp only [GeneralBorrowFreshMetadataChildMutable.result,GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  have newTagMutable : (GeneralBorrowExposedScopedProtectedMutableLeafPipeline.mutableInput prepared).newTag = input.newTag := newTagEq
  rw [childEq,newTagMutable] at result
  exact ⟨result⟩
end DuplicatePrefix.GeneralBorrowExposedScopedAsMutEntryReleaseData
