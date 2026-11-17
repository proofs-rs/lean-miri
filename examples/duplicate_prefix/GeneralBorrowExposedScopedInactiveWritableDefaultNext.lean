import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableDefaultRun
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableDefaultAdvance
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableDefaultNext
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildDefault
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedInactiveWritableDefaultConstructor (Resources ResourcesFor)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual full-range Read and shared construction yield the complete next
helper constructor resources, including the next fresh tag and allocator slot. -/
theorem next (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : Resources input protections selected head tail)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (future : BorTag) (futureFresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping future) (different : input.newTag ≠ future)
    (room : input.tree.nodes.size+2 < 65536) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    read.status = .Completed ∧ ∃ next : Input, next.tree = child.tree ∧ next.parentTag = input.newTag ∧ next.newTag = future ∧
      next.parent = index input ∧ next.offset = input.offset ∧ next.len = input.len ∧
      ∃ nextRaw : Resources next protections selected head tail,
        nextRaw.component.support = (fun position => raw.component.support position ∨ position = (index input).toNat) := by
  obtain ⟨readDone,prepared,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedInactiveWritableDefaultRun.prepare input protections selected head tail raw
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have mapping : prepared.tree.tagMapping = input.tree.tagMapping := by rw [treeEq];simpa only using congrArg BorrowTree.tagMapping frame
  have nodes : prepared.tree.nodes = input.tree.nodes := by rw [treeEq];simpa only using congrArg BorrowTree.nodes frame
  have nextFresh : GeneralBorrowTagMap.Fresh prepared.tree.tagMapping future := by rw [mapping];exact futureFresh
  obtain ⟨next,nextTree,nextParentTag,nextTag,nextParent,nextOffset,nextLen,nextRaw,nextSupport⟩ :=
    GeneralBorrowExposedScopedInactiveWritableDefaultAdvance.advance prepared protections selected head tail preparedRaw
      (by rw [offsetEq,lenEq];exact positive) future nextFresh (by rw [newTagEq];exact different)
      (by change prepared.tree.nodes.size+2<65536;rw [nodes];exact room)
  have childEq : result prepared =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree := by
    simp only [result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  let converted : Resources next protections selected head tail := {
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
  refine ⟨readDone,next,nextTree.trans childEq,nextParentTag.trans newTagEq,nextTag,nextParent.trans indexEq,
    nextOffset.trans offsetEq,nextLen.trans lenEq,converted,?_⟩
  simpa only [converted,supportEq,indexEq] using nextSupport

/-- Same-mode actual Default Read/construction pipeline; no window-to-global
selected exposure conversion is performed. -/
theorem next_mode {profileMode : ProfileMode} (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : ResourcesFor input protections selected head tail profileMode)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (future : BorTag) (futureFresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping future) (different : input.newTag ≠ future)
    (room : input.tree.nodes.size+2 < 65536) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    read.status = .Completed ∧ ∃ next : Input, next.tree = child.tree ∧ next.parentTag = input.newTag ∧ next.newTag = future ∧
      next.parent = index input ∧ next.offset = input.offset ∧ next.len = input.len ∧
      ∃ nextRaw : ResourcesFor next protections selected head tail profileMode,
        nextRaw.component.support = (fun position => raw.component.support position ∨ position = (index input).toNat) := by
  obtain ⟨readDone,prepared,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedInactiveWritableDefaultRun.prepare_mode input protections selected head tail raw
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have mapping : prepared.tree.tagMapping = input.tree.tagMapping := by rw [treeEq];simpa only using congrArg BorrowTree.tagMapping frame
  have nodes : prepared.tree.nodes = input.tree.nodes := by rw [treeEq];simpa only using congrArg BorrowTree.nodes frame
  have nextFresh : GeneralBorrowTagMap.Fresh prepared.tree.tagMapping future := by rw [mapping];exact futureFresh
  obtain ⟨next,nextTree,nextParentTag,nextTag,nextParent,nextOffset,nextLen,nextRaw,nextSupport⟩ :=
    GeneralBorrowExposedScopedInactiveWritableDefaultAdvance.advance_mode prepared protections selected head tail preparedRaw
      (by rw [offsetEq,lenEq];exact positive) future nextFresh (by rw [newTagEq];exact different)
      (by change prepared.tree.nodes.size+2<65536;rw [nodes];exact room)
  have childEq : result prepared =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree := by
    simp only [result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  let converted : ResourcesFor next protections selected head tail profileMode := {
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
  refine ⟨readDone,next,nextTree.trans childEq,nextParentTag.trans newTagEq,nextTag,nextParent.trans indexEq,
    nextOffset.trans offsetEq,nextLen.trans lenEq,converted,?_⟩
  simpa only [converted,supportEq,indexEq] using nextSupport
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableDefaultNext
