import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableSharedMetadata
import duplicate_prefix.GeneralBorrowFreshMetadataChildAllocator
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableSharedPathMetadata
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableSharedReadRelease
namespace DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableSharedReleaseAllocator
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedScopedWritableSharedConstructor (Resources)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

structure Output (input : Input) (after : BorrowTree) (future : BorTag) where
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates after
  noFree : after.tagMapping.deassigned.back?=none
  aligned : after.tagMapping.mapping.size=after.nodes.data.size
  nodeSize : after.nodes.size=input.tree.nodes.size+1
  roots : after.roots=input.tree.roots
  fresh : GeneralBorrowTagMap.Fresh after.tagMapping future
  well : after.locations.WellFormed
  capacity : after.locations.size=input.tree.locations.size

/-- Actual full-range helper construction/release retains the allocator and
future-tag reserve. Source metadata accounts for both permission-map splitting
and the new sparse node; no final allocator/freshness outcome is assumed. -/
theorem run (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (positive : input.offset.toNat<(input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (index input)=none) input.tree.locations)
    (future : BorTag) (futureFresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping future) (different : input.newTag≠future) :
    Nonempty (Output input ((GeneralBorrowExposedScopedWindowWritableSharedPathMetadata.child input protections .VisitChildrenOfAccessed).releaseProtector input.newTag protections).tree future) := by
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩:=
    GeneralBorrowExposedScopedWindowWritableSharedRun.prepare input protections selected head tail writable raw .VisitChildrenOfAccessed
  have readFrame:=GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have preparedFrame : prepared.tree={input.tree with locations:=prepared.tree.locations} := by rw [treeEq];exact readFrame
  have metadata:=append prepared
  have childEq : result prepared=GeneralBorrowExposedScopedWindowWritableSharedPathMetadata.child input protections .VisitChildrenOfAccessed := by
    simp only [result,GeneralBorrowExposedScopedWindowWritableSharedPathMetadata.child,treeEq,parentTagEq,newTagEq,offsetEq,lenEq,protectedEq]
  have freshPrepared : GeneralBorrowTagMap.Fresh prepared.tree.tagMapping future := by rw [preparedFrame];exact futureFresh
  have fresh:=GeneralBorrowFreshMetadataChildAllocator.append_fresh prepared future freshPrepared (by rw [newTagEq];exact different)
  have release:=GeneralBorrowExposedScopedWindowWritableSharedReadRelease.release input protections selected head tail writable raw positive clean
  rw [←childEq]
  have frame:=GeneralBorrowStructuralReleaseGeometryFrame.release (result prepared) protections input.newTag
  refine ⟨⟨?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · rw [frame];exact ⟨metadata.certificates.depth,metadata.certificates.children,metadata.certificates.covered⟩
  · rw [frame];exact metadata.noFree
  · rw [frame];exact metadata.aligned
  · rw [frame,metadata.size,preparedFrame]
  · rw [frame,metadata.roots,preparedFrame]
  · rw [frame];exact fresh
  · rw [childEq];exact release.2.2.1
  · rw [childEq];exact release.2.2.2
end DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableSharedReleaseAllocator
