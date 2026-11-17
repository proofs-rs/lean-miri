import duplicate_prefix.GeneralBorrowPositiveConcreteWindowVacantClean
import duplicate_prefix.GeneralBorrowExposedScopedProtectedMutableActivity
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowFnEntryActivity
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures
open GeneralBorrowFreshActiveWithin
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
/-- Real parent Read and protected FnEntry construction confine the new child's
Read activity to the actual slice, using initial vacant permission cleanliness. -/
theorem source_read {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode)
    (clean : GeneralBorrowGcVacantClean.VacantClean s.entry.allocation.extra) :
    ActiveWithin (GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree
      s.entry.allocation.extra s.tracker s.parentTag s.offset s.len)
      (GeneralBorrowFreshMetadataChildMutable.index s.data.input) .Read s.offset (s.offset+s.len) := by
  obtain ⟨held,support⟩ := GeneralBorrowExposedScopedInactiveWritableMutableEntryInput.register
    s.data.input s.tracker.global.protectedTags s.selected s.head s.extraRoots s.data.resources
    (by simpa only [s.data.treeEq] using s.data.nodeTags)
  let protections := s.tracker.global.protectedTags.insert s.data.input.newTag .StrongProtector
  obtain ⟨context,owned⟩ := GeneralBorrowExposedScopedInactiveWritableProtectedMutableData.build
    s.data.input protections s.selected s.head s.extraRoots held
  obtain ⟨completed,next,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,nextRaw,nextSupport⟩ :=
    GeneralBorrowExposedScopedInactiveWindowWritableProtectedMutableRun.prepare
      s.data.input protections s.selected s.head s.extraRoots held.toWindow
  let read := s.data.input.tree.performBorrowAccessRange (.concrete s.data.input.parentTag)
    (Size.ofBytes s.data.input.offset) (Size.ofBytes s.data.input.len) .Read protections .VisitChildrenOfAccessed
  have frame := GeneralBorrowFreshReadFrame.frame s.data.input.tree (.concrete s.data.input.parentTag)
    (Size.ofBytes s.data.input.offset) (Size.ofBytes s.data.input.len) .Read protections .VisitChildrenOfAccessed
  have nodes : next.tree.nodes=s.data.input.tree.nodes := by
    rw [treeEq];simpa only using congrArg BorrowTree.nodes frame
  have nodeFits : s.data.input.tree.nodes.data.size≤4294967296 := by
    have bound:=s.data.input.fits;have aligned:=s.data.input.aligned;omega
  have nextClean : GeneralBorrowGcVacantClean.VacantClean next.tree := by
    intro query vacant
    have initialVacant : s.data.input.tree.nodes.get query=none := by rw [←nodes];exact vacant
    have initialClean := clean query (by simpa only [s.data.treeEq] using initialVacant)
    have accessed := GeneralBorrowExposedScopedInactiveWritableCleanReadRange.ranged
      s.data.input.tree protections s.data.input.parentTag s.data.input.parent s.selected s.head query s.extraRoots
      (Size.ofBytes s.data.input.offset) (Size.ofBytes s.data.input.len) context held.component.support (fun _=>true)
      nodeFits s.data.input.parentTagPresent initialVacant
      (by simpa only [GeneralBorrowFreshFutureClean.Clean,s.data.treeEq] using initialClean) s.data.input.well s.data.input.offset
      (s.data.input.offset+s.data.input.len) owned s.data.input.bounds (Nat.le_refl _) (Nat.le_refl _)
    rw [treeEq]
    exact accessed.2
  have atEnd := GeneralBorrowFreshMetadataChildMutable.at_end next
  have vacant : next.tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index next)=none := by
    unfold UniValMap.get
    rw [atEnd]
    simp
  have activity := GeneralBorrowExposedScopedProtectedMutableActivity.append next.tree next.depth
    next.parentTag next.newTag next.parent next.parentNode next.parentTagPresent next.parentPresent
    next.fresh next.noFree next.aligned next.fits next.offset next.len next.nonzero next.well next.bounds
    (nextClean _ vacant)
  change ActiveWithin (GeneralBorrowFreshMetadataChildMutable.result next)
    (GeneralBorrowFreshMetadataChildMutable.index next) .Read next.offset (next.offset+next.len) at activity
  rw [indexEq] at activity
  simpa only [GeneralBorrowFreshMetadataChildMutable.result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq,
    s.data.treeEq,s.data.parentTagEq,s.data.newTagEq,s.data.offsetEq,s.data.lenEq,
    GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree,TypedBorrowSteps.registeredGlobal,protections] using activity

theorem source {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode)
    (clean : GeneralBorrowGcVacantClean.VacantClean s.entry.allocation.extra) :
    ActiveWithin (GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree
      s.entry.allocation.extra s.tracker s.parentTag s.offset s.len)
      (GeneralBorrowFreshMetadataChildMutable.index s.data.input) .Write s.offset (s.offset+s.len) :=
  GeneralBorrowFreshActiveWithin.to_write _ _ _ _ (source_read s clean)
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowFnEntryActivity
