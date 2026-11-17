import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedRun
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedAdvance
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedNext
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedInactiveWritableSharedConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual window Read and shared construction yield the complete next
helper constructor resources, including the next fresh tag and allocator slot. -/
theorem next (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (future : BorTag) (futureFresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping future) (different : input.newTag ≠ future)
    (room : input.tree.nodes.size+2 < 65536) (held : Bool) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected
    read.status = .Completed ∧ ∃ next : Input, next.tree = child.tree ∧ next.parentTag = input.newTag ∧ next.newTag = future ∧
      next.parent = index input ∧ next.isProtected = held ∧ next.offset = input.offset ∧ next.len = input.len ∧
      ∃ nextRaw : Resources next protections selected head tail (GeneralBorrowFreshMixedChild.extend writable (index input).toNat),
        nextRaw.component.support = (fun position => raw.component.support position ∨ position = (index input).toNat) := by
  obtain ⟨readDone,prepared,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedInactiveWritableSharedRun.prepare input protections selected head tail writable raw
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have mapping : prepared.tree.tagMapping = input.tree.tagMapping := by rw [treeEq];simpa only using congrArg BorrowTree.tagMapping frame
  have nodes : prepared.tree.nodes = input.tree.nodes := by rw [treeEq];simpa only using congrArg BorrowTree.nodes frame
  have nextFresh : GeneralBorrowTagMap.Fresh prepared.tree.tagMapping future := by rw [mapping];exact futureFresh
  obtain ⟨next,nextTree,nextParentTag,nextTag,nextParent,nextProtected,nextOffset,nextLen,nextRaw,nextSupport⟩ :=
    GeneralBorrowExposedScopedInactiveWritableSharedAdvance.advance prepared protections selected head tail writable preparedRaw
      (by rw [offsetEq,lenEq];exact positive) future nextFresh (by rw [newTagEq];exact different)
      (by change prepared.tree.nodes.size+2<65536;rw [nodes];exact room) held
  have childEq : result prepared =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected).tree := by
    simp only [result,treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq]
  let converted : Resources next protections selected head tail (GeneralBorrowFreshMixedChild.extend writable (index input).toNat) := {
    forest := nextRaw.forest
    component := nextRaw.component
    selectedNode := nextRaw.selectedNode
    selectedPresent := nextRaw.selectedPresent
    roots := nextRaw.roots
    rootPath := nextRaw.rootPath
    exposures := nextRaw.exposures
    separate := nextRaw.separate
    tags := nextRaw.tags
    leaves := nextRaw.leaves
    writableLeaves := nextRaw.writableLeaves
    first := nextRaw.first
    rest := nextRaw.rest
    coherent := nextRaw.coherent
    owned := by simpa only [indexEq] using nextRaw.owned
    room := nextRaw.room }
  refine ⟨readDone,next,nextTree.trans childEq,nextParentTag.trans newTagEq,nextTag,nextParent.trans indexEq,nextProtected,
    nextOffset.trans offsetEq,nextLen.trans lenEq,converted,?_⟩
  simpa only [converted,supportEq,indexEq] using nextSupport

/-- Actual next-helper formation preserves the explicit selected-profile scope. -/
theorem next_mode {profileMode : ProfileMode} (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor input protections selected head tail writable profileMode)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (future : BorTag) (futureFresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping future) (different : input.newTag ≠ future)
    (room : input.tree.nodes.size+2 < 65536) (held : Bool) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected
    read.status = .Completed ∧ ∃ next : Input, next.tree = child.tree ∧ next.parentTag = input.newTag ∧ next.newTag = future ∧
      next.parent = index input ∧ next.isProtected = held ∧ next.offset = input.offset ∧ next.len = input.len ∧
      ∃ nextRaw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor next protections selected head tail (GeneralBorrowFreshMixedChild.extend writable (index input).toNat) profileMode,
        nextRaw.component.support = (fun position => raw.component.support position ∨ position = (index input).toNat) := by
  obtain ⟨readDone,prepared,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedInactiveWritableSharedRun.prepare_mode input protections selected head tail writable raw
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have mapping : prepared.tree.tagMapping = input.tree.tagMapping := by rw [treeEq];simpa only using congrArg BorrowTree.tagMapping frame
  have nodes : prepared.tree.nodes = input.tree.nodes := by rw [treeEq];simpa only using congrArg BorrowTree.nodes frame
  have nextFresh : GeneralBorrowTagMap.Fresh prepared.tree.tagMapping future := by rw [mapping];exact futureFresh
  obtain ⟨next,nextTree,nextParentTag,nextTag,nextParent,nextProtected,nextOffset,nextLen,nextRaw,nextSupport⟩ :=
    GeneralBorrowExposedScopedInactiveWritableSharedAdvance.advance_mode prepared protections selected head tail writable preparedRaw
      (by rw [offsetEq,lenEq];exact positive) future nextFresh (by rw [newTagEq];exact different)
      (by change prepared.tree.nodes.size+2<65536;rw [nodes];exact room) held
  have childEq : result prepared =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected).tree := by
    simp only [result,treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq]
  let converted : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor next protections selected head tail (GeneralBorrowFreshMixedChild.extend writable (index input).toNat) profileMode := {
    forest := nextRaw.forest
    component := nextRaw.component
    selectedNode := nextRaw.selectedNode
    selectedPresent := nextRaw.selectedPresent
    roots := nextRaw.roots
    rootPath := nextRaw.rootPath
    exposures := nextRaw.exposures
    separate := nextRaw.separate
    tags := nextRaw.tags
    leaves := nextRaw.leaves
    writableLeaves := nextRaw.writableLeaves
    first := nextRaw.first
    rest := nextRaw.rest
    coherent := nextRaw.coherent
    owned := by simpa only [indexEq] using nextRaw.owned
    room := nextRaw.room }
  refine ⟨readDone,next,nextTree.trans childEq,nextParentTag.trans newTagEq,nextTag,nextParent.trans indexEq,nextProtected,
    nextOffset.trans offsetEq,nextLen.trans lenEq,converted,?_⟩
  simpa only [converted,supportEq,indexEq] using nextSupport
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedNext
