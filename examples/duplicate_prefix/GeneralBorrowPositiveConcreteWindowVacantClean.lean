import duplicate_prefix.GeneralBorrowPositiveConcreteWindowOriginalInput
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableMutableEntryInput
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWindowWritableProtectedMutableRun
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableCleanReadRange
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableOld
import duplicate_prefix.GeneralBorrowFreshFutureClean
import duplicate_prefix.GeneralBorrowGcVacantClean
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowVacantClean
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
omit area in
private theorem append_clean (input : GeneralBorrowFreshMetadataChildMutable.Input)
    (clean : GeneralBorrowGcVacantClean.VacantClean input.tree) :
    GeneralBorrowGcVacantClean.VacantClean (GeneralBorrowFreshMetadataChildMutable.result input) := by
  intro query vacant
  have different : query≠GeneralBorrowFreshMetadataChildMutable.index input := by
    intro same
    obtain ⟨node,present,rest⟩ := (GeneralBorrowFreshMetadataChildMutable.append input).newNode
    change (GeneralBorrowFreshMetadataChildMutable.result input).nodeAt query=none at vacant
    rw [same,present] at vacant
    cases vacant
  have oldVacant : input.tree.nodes.get query=none := by
    cases old : input.tree.nodes.get query with
    | none => rfl
    | some node =>
      obtain ⟨next,present,rest⟩ := GeneralBorrowFreshMetadataChildMutableOld.append input query node old
      change (GeneralBorrowFreshMetadataChildMutable.result input).nodeAt query=none at vacant
      rw [vacant] at present
      cases present
  have modified := GeneralBorrowFreshFutureClean.modified input.tree.locations
    (GeneralBorrowFreshMetadataChildMutable.index input) query (Size.ofBytes input.offset) (Size.ofBytes input.len)
    GeneralBorrowFreshChild.inside different input.well input.bounds (clean query oldVacant)
  have stageClean : GeneralBorrowFreshFutureClean.Clean (GeneralBorrowFreshMetadataChildMutable.stage input) query := modified
  exact GeneralBorrowFreshFutureClean.shape_preserves _ _ (GeneralBorrowFreshMetadataChildMutable.shape input) query stageClean

/-- Allocation-wide vacant permissions survive actual concrete parent Read,
fresh Strong registration and the protected FnEntry child, from initial Clean. -/
theorem preserves {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode)
    (clean : GeneralBorrowGcVacantClean.VacantClean s.entry.allocation.extra) :
    GeneralBorrowGcVacantClean.VacantClean
      (GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree
        s.entry.allocation.extra s.tracker s.parentTag s.offset s.len) := by
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
  have afterClean := append_clean next nextClean
  simpa only [GeneralBorrowFreshMetadataChildMutable.result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq,
    s.data.treeEq,s.data.parentTagEq,s.data.newTagEq,s.data.offsetEq,s.data.lenEq,
    GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree,TypedBorrowSteps.registeredGlobal,protections] using afterClean
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowVacantClean
