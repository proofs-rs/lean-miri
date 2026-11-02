import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableLenCallInput
namespace DuplicatePrefix.GeneralBorrowScopedWindowWritableLenTargetMetadata
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildShared GeneralBorrowExposedScopedSharedPathMetadata
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

def held (s : GeneralBorrowExposedScopedWindowWritableLenCallInput.Input) :=
  TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker s.tracker s.fresh) s.tracker.global.nextPointerTag

def tree (s : GeneralBorrowExposedScopedWindowWritableLenCallInput.Input) :=
  ((GeneralBorrowExposedScopedSharedArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.exprTag s.offset s.len).releaseProtector
    s.tracker.global.nextPointerTag (held s).global.protectedTags).tree

/-- The actual two shared constructors and helper release retain the original
physical target tag/hidden flag and derive its finite node capacity. -/
theorem source (s : GeneralBorrowExposedScopedWindowWritableLenCallInput.Input) :
    (∃ node,(tree s).nodeAt s.first.parent=some node ∧ node.tag=s.first.parentNode.tag ∧ node.isExposed=false) ∧
    (tree s).nodes.data.size≤4294967296 := by
  let tags:=(held s).global.protectedTags
  let raw : GeneralBorrowExposedScopedWritableSharedConstructor.Resources s.input tags s.selected s.head s.tail s.writable := s.raw
  have first:=GeneralBorrowExposedScopedWindowWritableSharedMetadata.run s.first s.firstTags s.selected s.head s.tail (fun _=>true)
    s.firstRaw s.initialTags
  obtain ⟨middle,found,middleTag,middleFlag⟩:=first.2.2.2.2 s.first.parent s.first.parentNode s.first.parentPresent
  have firstFrame:=GeneralBorrowStructuralReleaseGeometryFrame.release (child s.first s.firstTags .VisitChildrenOfAccessed) s.firstTags s.first.newTag
  have middlePresent : s.input.tree.nodeAt s.first.parent=some middle := by
    rw [s.firstTreeEq]
    change ((child s.first s.firstTags .VisitChildrenOfAccessed).releaseProtector s.first.newTag s.firstTags).tree.nodeAt s.first.parent=some middle at found
    rw [firstFrame] at found
    exact found
  have inputTags : GeneralBorrowGcAllocator.NodeTags s.input.tree := by rw [s.firstTreeEq];exact first.1
  have second:=GeneralBorrowExposedScopedWindowWritableSharedMetadata.run s.input tags s.selected s.head s.tail s.writable raw inputTags
  obtain ⟨final,present,tag,flag⟩:=second.2.2.2.2 s.first.parent middle middlePresent
  have childEq : child s.input tags .VisitChildrenOfAccessed=
      GeneralBorrowExposedScopedSharedArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.exprTag s.offset s.len := by
    simp only [child,GeneralBorrowExposedScopedSharedArgumentCopy.finalTree,s.treeEq,s.parentTagEq,s.tagEq,s.offsetEq,s.lenEq,s.protectedEq]
    rfl
  have target : ∃ node,(tree s).nodeAt s.first.parent=some node ∧ node.tag=s.first.parentNode.tag ∧ node.isExposed=false := by
    refine ⟨final,?_,tag.trans middleTag,?_⟩
    · change ((child s.input tags .VisitChildrenOfAccessed).releaseProtector s.input.newTag tags).tree.nodeAt s.first.parent=some final at present
      rw [childEq,s.tagEq] at present
      exact present
    · rw [flag,middleFlag]
      exact s.firstRaw.hidden s.first.parent s.first.parentNode s.firstRaw.component.anchor s.first.parentPresent
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩:=
    GeneralBorrowExposedScopedWindowWritableSharedRun.prepare s.input tags s.selected s.head s.tail s.writable raw .VisitChildrenOfAccessed
  have frame:=GeneralBorrowFreshReadFrame.frame s.input.tree (.concrete s.input.parentTag) (Size.ofBytes s.input.offset) (Size.ofBytes s.input.len) .Read tags .VisitChildrenOfAccessed
  have prepNodes : prepared.tree.nodes=s.input.tree.nodes := by rw [treeEq,frame]
  have preparedChildEq : result prepared=child s.input tags .VisitChildrenOfAccessed := by
    simp only [result,child,treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq]
  have releaseFrame:=GeneralBorrowStructuralReleaseGeometryFrame.release
    (GeneralBorrowExposedScopedSharedArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.exprTag s.offset s.len) tags s.tracker.global.nextPointerTag
  have size : (tree s).nodes.size=s.input.tree.nodes.size+1 := by
    change ((GeneralBorrowExposedScopedSharedArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.exprTag s.offset s.len).releaseProtector s.tracker.global.nextPointerTag tags).tree.nodes.size=_
    rw [releaseFrame,←childEq,←preparedChildEq,(append prepared).size,prepNodes]
  refine ⟨target,?_⟩
  change (tree s).nodes.size≤4294967296
  rw [size]
  have bound:=s.raw.room
  omega
end
end DuplicatePrefix.GeneralBorrowScopedWindowWritableLenTargetMetadata
