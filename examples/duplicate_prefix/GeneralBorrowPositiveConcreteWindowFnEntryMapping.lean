import duplicate_prefix.GeneralBorrowPositiveConcreteWindowFnEntryNode
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowFnEntryMapping
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Exact allocator mapping of the real protected FnEntry child, from original
raw caller data. The parent Read leaves the map unchanged; the constructor adds
exactly its actual tag/index row. No poststate or operation success is assumed. -/
theorem source {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode) :
    (GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree
      s.entry.allocation.extra s.tracker s.parentTag s.offset s.len).tagMapping=
    ⟨s.entry.allocation.extra.tagMapping.mapping.push
      (s.tracker.global.nextPointerTag,GeneralBorrowFreshMetadataChildMutable.index s.data.input),
      s.entry.allocation.extra.tagMapping.deassigned⟩ := by
  obtain ⟨held,support⟩ := GeneralBorrowExposedScopedInactiveWritableMutableEntryInput.register
    s.data.input s.tracker.global.protectedTags s.selected s.head s.extraRoots s.data.resources
    (by simpa only [s.data.treeEq] using s.data.nodeTags)
  let protections := s.tracker.global.protectedTags.insert s.data.input.newTag .StrongProtector
  obtain ⟨done,next,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,nextRaw,nextSupport⟩ :=
    GeneralBorrowExposedScopedInactiveWindowWritableProtectedMutableRun.prepare
      s.data.input protections s.selected s.head s.extraRoots held.toWindow
  have frame := GeneralBorrowFreshReadFrame.frame s.data.input.tree (.concrete s.data.input.parentTag)
    (Size.ofBytes s.data.input.offset) (Size.ofBytes s.data.input.len) .Read protections .VisitChildrenOfAccessed
  have readMap : next.tree.tagMapping=s.data.input.tree.tagMapping := by
    rw [treeEq];simpa only using congrArg BorrowTree.tagMapping frame
  have mapped := (GeneralBorrowFreshMetadataChildMutable.append next).mapping
  rw [GeneralBorrowFreshMetadataChildMutable.mapping,readMap,indexEq,newTagEq] at mapped
  simpa only [GeneralBorrowFreshMetadataChildMutable.result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq,
    s.data.treeEq,s.data.parentTagEq,s.data.newTagEq,s.data.offsetEq,s.data.lenEq,
    GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree,TypedBorrowSteps.registeredGlobal,protections] using mapped
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowFnEntryMapping
