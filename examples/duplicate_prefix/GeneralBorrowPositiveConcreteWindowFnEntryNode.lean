import duplicate_prefix.GeneralBorrowPositiveConcreteWindowOriginalInput
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableMutableEntryInput
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWindowWritableProtectedMutableRun
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowFnEntryNode
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- The actual protected FnEntry child is present, has the freshly allocated
tag, and is hidden. All facts follow from initial raw resources; no inverse
NodeTags assumption, history witness or constructor outcome is supplied. -/
theorem source {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode) :
    ∃ node,(GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree
      s.entry.allocation.extra s.tracker s.parentTag s.offset s.len).nodeAt
      (GeneralBorrowFreshMetadataChildMutable.index s.data.input)=some node ∧
      node.tag=s.tracker.global.nextPointerTag ∧node.isExposed=false := by
  obtain ⟨held,support⟩ := GeneralBorrowExposedScopedInactiveWritableMutableEntryInput.register
    s.data.input s.tracker.global.protectedTags s.selected s.head s.extraRoots s.data.resources
    (by simpa only [s.data.treeEq] using s.data.nodeTags)
  let protections := s.tracker.global.protectedTags.insert s.data.input.newTag .StrongProtector
  obtain ⟨done,next,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,nextRaw,nextSupport⟩ :=
    GeneralBorrowExposedScopedInactiveWindowWritableProtectedMutableRun.prepare
      s.data.input protections s.selected s.head s.extraRoots held.toWindow
  obtain ⟨node,present,tag,parent,children,permission,hidden⟩ :=
    (GeneralBorrowFreshMetadataChildMutable.append next).newNode
  refine ⟨node,?_,?_,hidden⟩
  · rw [indexEq] at present
    simpa only [GeneralBorrowFreshMetadataChildMutable.result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq,
      s.data.treeEq,s.data.parentTagEq,s.data.newTagEq,s.data.offsetEq,s.data.lenEq,
      GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree,TypedBorrowSteps.registeredGlobal,protections] using present
  · exact tag.trans (newTagEq.trans s.data.newTagEq)
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowFnEntryNode
