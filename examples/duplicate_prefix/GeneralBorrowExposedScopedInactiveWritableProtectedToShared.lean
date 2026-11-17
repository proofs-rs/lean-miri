import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedToSharedAdvance
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableRun
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableProtectedMutableProtect
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedProtect
import duplicate_prefix.GeneralBorrowExposedScopedWritableProtectedMutableGraphMetadata
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableProtectedToShared
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildMutable
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem prepare (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedInactiveWritableProtectedMutableConstructor.Resources input protections selected head tail)
    (nodeTags : GeneralBorrowGcAllocator.NodeTags input.tree)
    (positive : input.offset.toNat<(input.offset+input.len).toNat)
    (slotTag future : BorTag)
    (slotFresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping slotTag)
    (futureFresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping future)
    (slotDifferent : input.newTag≠slotTag) (different : input.newTag≠future)
    (room : input.tree.nodes.size+2<65536) :
    let held := protections.insert input.newTag .StrongProtector
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read held .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    read.status=.Completed ∧ child.outcome=.ok () ∧
    ∃ next : GeneralBorrowFreshMetadataChildShared.Input,
      next.tree=child.tree ∧ next.parentTag=input.newTag ∧ next.newTag=future ∧ next.parent=index input ∧
      next.offset=input.offset ∧ next.len=input.len ∧ next.isProtected=false ∧
      ∃ resources : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.Resources next
        (held.insert slotTag .StrongProtector) selected head tail (fun _=>true),
        resources.component.support=(fun position=>raw.component.support position∨position=(index input).toNat) := by
  obtain ⟨held,supportHeld⟩:=GeneralBorrowExposedScopedInactiveWritableProtectedMutableProtect.protect input protections input.newTag selected head tail raw (by
    intro query node present same
    have mapped:=nodeTags query node present
    have absent : input.tree.tagMapping.get input.newTag=none := by
      simp only [UniKeyMap.get,GeneralBorrowTagMap.fresh_find input.tree.tagMapping input.newTag input.fresh,Option.map_none]
    rw [same,absent] at mapped
    cases mapped)
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩:=
    GeneralBorrowExposedScopedInactiveWritableProtectedMutableRun.prepare input _ selected head tail held
  have frame:=GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read
    (protections.insert input.newTag .StrongProtector) .VisitChildrenOfAccessed
  have preparedTags : GeneralBorrowGcAllocator.NodeTags prepared.tree := by
    intro query node present
    rw [treeEq,frame] at present ⊢
    exact nodeTags query node present
  have freshFuture : GeneralBorrowTagMap.Fresh prepared.tree.tagMapping future := by rw [treeEq,frame];exact futureFresh
  obtain ⟨next,nextTree,parentTag,newTag,parent,offset,len,nextRaw,nextSupport⟩:=
    GeneralBorrowExposedScopedInactiveWritableProtectedToSharedAdvance.advance prepared _ selected head tail preparedRaw
      (by simpa only [offsetEq,lenEq] using positive) future freshFuture (by simpa only [newTagEq] using different)
      (by rw [treeEq,frame];exact room)
  have slotAbsent : next.tree.tagMapping.get slotTag=none := by
    have fresh : GeneralBorrowTagMap.Fresh prepared.tree.tagMapping slotTag := by rw [treeEq,frame];exact slotFresh
    rw [nextTree,(append prepared).mapping]
    have absent:=GeneralBorrowFreshMetadataChildAllocator.fresh_push prepared.tree.tagMapping prepared.newTag slotTag (index prepared)
      prepared.tree.tagMapping.deassigned fresh (by simpa only [newTagEq] using slotDifferent)
    simp only [mapping,UniKeyMap.get,GeneralBorrowTagMap.fresh_find _ _ absent,Option.map_none]
  have nextTags : GeneralBorrowGcAllocator.NodeTags next.tree := by
    rw [nextTree]
    exact GeneralBorrowExposedScopedWritableProtectedMutableGraphMetadata.construct_nodeTags prepared preparedTags
  obtain ⟨registered,registeredSupport⟩:=GeneralBorrowExposedScopedInactiveWritableSharedProtect.protect next _ slotTag selected head tail (fun _=>true) nextRaw (by
    intro query node present same
    have mapped:=nextTags query node present
    rw [same,slotAbsent] at mapped
    cases mapped)
  have childEq : result prepared =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read
        (protections.insert input.newTag .StrongProtector) .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree := by
    simp only [result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  let unprotected : GeneralBorrowFreshMetadataChildShared.Input := {next with isProtected:=false}
  let unprotectedRaw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.Resources unprotected
      ((protections.insert input.newTag .StrongProtector).insert slotTag .StrongProtector) selected head tail (fun _=>true) := {
    forest:=registered.forest,component:=registered.component,selectedNode:=registered.selectedNode,selectedPresent:=registered.selectedPresent,
    roots:=registered.roots,rootPath:=registered.rootPath,exposures:=registered.exposures,separate:=registered.separate,tags:=registered.tags,
    leaves:=registered.leaves,writableLeaves:=registered.writableLeaves,first:=registered.first,rest:=registered.rest,
    coherent:=registered.coherent,owned:=registered.owned,room:=registered.room }
  have success:=(append prepared).success
  refine ⟨done,?_,unprotected,nextTree.trans childEq,parentTag.trans newTagEq,newTag,parent.trans indexEq,offset.trans offsetEq,len.trans lenEq,rfl,unprotectedRaw,?_⟩
  · simpa only [treeEq,parentTagEq,newTagEq,offsetEq,lenEq] using success
  · change registered.component.support=_
    rw [registeredSupport,nextSupport,supportEq,supportHeld,indexEq]

/-- Actual next-helper formation preserves the explicit selected-profile scope. -/
theorem prepare_mode {profileMode : ProfileMode} (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedInactiveWritableProtectedMutableConstructor.ResourcesFor input protections selected head tail profileMode)
    (nodeTags : GeneralBorrowGcAllocator.NodeTags input.tree)
    (positive : input.offset.toNat<(input.offset+input.len).toNat)
    (slotTag future : BorTag)
    (slotFresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping slotTag)
    (futureFresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping future)
    (slotDifferent : input.newTag≠slotTag) (different : input.newTag≠future)
    (room : input.tree.nodes.size+2<65536) :
    let held := protections.insert input.newTag .StrongProtector
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read held .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    read.status=.Completed ∧ child.outcome=.ok () ∧
    ∃ next : GeneralBorrowFreshMetadataChildShared.Input,
      next.tree=child.tree ∧ next.parentTag=input.newTag ∧ next.newTag=future ∧ next.parent=index input ∧
      next.offset=input.offset ∧ next.len=input.len ∧ next.isProtected=false ∧
      ∃ resources : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor next
        (held.insert slotTag .StrongProtector) selected head tail (fun _=>true) profileMode,
        resources.component.support=(fun position=>raw.component.support position∨position=(index input).toNat) := by
  obtain ⟨held,supportHeld⟩:=GeneralBorrowExposedScopedInactiveWritableProtectedMutableProtect.protect input protections input.newTag selected head tail raw (by
    intro query node present same
    have mapped:=nodeTags query node present
    have absent : input.tree.tagMapping.get input.newTag=none := by
      simp only [UniKeyMap.get,GeneralBorrowTagMap.fresh_find input.tree.tagMapping input.newTag input.fresh,Option.map_none]
    rw [same,absent] at mapped
    cases mapped)
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩:=
    GeneralBorrowExposedScopedInactiveWritableProtectedMutableRun.prepare_mode input _ selected head tail held
  have frame:=GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read
    (protections.insert input.newTag .StrongProtector) .VisitChildrenOfAccessed
  have preparedTags : GeneralBorrowGcAllocator.NodeTags prepared.tree := by
    intro query node present
    rw [treeEq,frame] at present ⊢
    exact nodeTags query node present
  have freshFuture : GeneralBorrowTagMap.Fresh prepared.tree.tagMapping future := by rw [treeEq,frame];exact futureFresh
  obtain ⟨next,nextTree,parentTag,newTag,parent,offset,len,nextRaw,nextSupport⟩:=
    GeneralBorrowExposedScopedInactiveWritableProtectedToSharedAdvance.advance_mode prepared _ selected head tail preparedRaw
      (by simpa only [offsetEq,lenEq] using positive) future freshFuture (by simpa only [newTagEq] using different)
      (by rw [treeEq,frame];exact room)
  have slotAbsent : next.tree.tagMapping.get slotTag=none := by
    have fresh : GeneralBorrowTagMap.Fresh prepared.tree.tagMapping slotTag := by rw [treeEq,frame];exact slotFresh
    rw [nextTree,(append prepared).mapping]
    have absent:=GeneralBorrowFreshMetadataChildAllocator.fresh_push prepared.tree.tagMapping prepared.newTag slotTag (index prepared)
      prepared.tree.tagMapping.deassigned fresh (by simpa only [newTagEq] using slotDifferent)
    simp only [mapping,UniKeyMap.get,GeneralBorrowTagMap.fresh_find _ _ absent,Option.map_none]
  have nextTags : GeneralBorrowGcAllocator.NodeTags next.tree := by
    rw [nextTree]
    exact GeneralBorrowExposedScopedWritableProtectedMutableGraphMetadata.construct_nodeTags prepared preparedTags
  obtain ⟨registered,registeredSupport⟩:=GeneralBorrowExposedScopedInactiveWritableSharedProtect.protect next _ slotTag selected head tail (fun _=>true) nextRaw (by
    intro query node present same
    have mapped:=nextTags query node present
    rw [same,slotAbsent] at mapped
    cases mapped)
  have childEq : result prepared =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read
        (protections.insert input.newTag .StrongProtector) .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree := by
    simp only [result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  let unprotected : GeneralBorrowFreshMetadataChildShared.Input := {next with isProtected:=false}
  let unprotectedRaw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor unprotected
      ((protections.insert input.newTag .StrongProtector).insert slotTag .StrongProtector) selected head tail (fun _=>true) profileMode := {
    forest:=registered.forest,component:=registered.component,selectedNode:=registered.selectedNode,selectedPresent:=registered.selectedPresent,
    roots:=registered.roots,rootPath:=registered.rootPath,exposures:=registered.exposures,separate:=registered.separate,tags:=registered.tags,
    leaves:=registered.leaves,writableLeaves:=registered.writableLeaves,first:=registered.first,rest:=registered.rest,
    coherent:=registered.coherent,owned:=registered.owned,room:=registered.room }
  have success:=(append prepared).success
  refine ⟨done,?_,unprotected,nextTree.trans childEq,parentTag.trans newTagEq,newTag,parent.trans indexEq,offset.trans offsetEq,len.trans lenEq,rfl,unprotectedRaw,?_⟩
  · simpa only [treeEq,parentTagEq,newTagEq,offsetEq,lenEq] using success
  · change registered.component.support=_
    rw [registeredSupport,nextSupport,supportEq,supportHeld,indexEq]
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableProtectedToShared
