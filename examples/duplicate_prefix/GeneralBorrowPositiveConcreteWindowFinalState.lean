import duplicate_prefix.GeneralBorrowPositiveConcreteWindowOriginalInput
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw
import duplicate_prefix.GeneralBorrowStructuralHistoryFrames
import duplicate_prefix.GeneralBorrowStructuralHistoryMutable
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowFinalState
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.DataStructures
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Intrinsic graph/allocator state and exact capacity after the actual concrete
parent Read and protected FnEntry child. Borrow permission success is separate. -/
theorem build {profileMode : ProfileMode} (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode) :
    let after := GeneralBorrowExposedScopedInactiveWritableMutableArgumentRaw.finalTree
      s.entry.allocation.extra s.tracker s.parentTag s.offset s.len
    GeneralBorrowStructuralHistoryState.State after ∧
      after.locations.size=s.entry.allocation.extra.locations.size ∧
      after.nodes.size≤s.entry.allocation.extra.nodes.size+1 := by
  let tree := s.entry.allocation.extra
  let protections := (TypedBorrowSteps.registeredGlobal s.tracker s.tracker.global.nextPointerTag).protectedTags
  let read := tree.performBorrowAccessRange (.concrete s.parentTag) (Size.ofBytes s.offset)
    (Size.ofBytes s.len) .Read protections .VisitChildrenOfAccessed
  have bounds : s.offset.toNat+s.len.toNat≤tree.locations.size.bytes.toNat := by
    rw [s.allocationCapacity];exact s.bounds
  have accessed := GeneralBorrowStructuralHistoryFrames.access tree s.initialState
    (.concrete s.parentTag) (Size.ofBytes s.offset) (Size.ofBytes s.len) .Read protections .VisitChildrenOfAccessed bounds
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete s.parentTag) (Size.ofBytes s.offset)
    (Size.ofBytes s.len) .Read protections .VisitChildrenOfAccessed
  have mapping : read.tree.tagMapping=tree.tagMapping := by
    simpa only using congrArg BorrowTree.tagMapping frame
  have nodes : read.tree.nodes=tree.nodes := by
    simpa only using congrArg BorrowTree.nodes frame
  have inputTree : s.data.input.tree=tree := s.data.treeEq
  have parentTag : read.tree.indexOfTag s.parentTag=some s.data.input.parent := by
    rw [BorrowTree.indexOfTag,mapping]
    have h:=s.data.input.parentTagPresent
    rw [inputTree,s.data.parentTagEq] at h
    exact h
  have parentNode : read.tree.nodeAt s.data.input.parent=some s.data.input.parentNode := by
    have h:=s.data.input.parentPresent
    rw [inputTree] at h
    simpa only [BorrowTree.nodeAt,nodes] using h
  have fresh : GeneralBorrowTagMap.Fresh read.tree.tagMapping s.tracker.global.nextPointerTag := by
    rw [mapping];exact s.tagFresh
  have room : read.tree.nodes.size+1≤4294967295 := by
    rw [nodes];have h:=s.nodeRoom;change s.entry.allocation.extra.nodes.size+1≤4294967295;omega
  have afterBounds : s.offset.toNat+s.len.toNat≤read.tree.locations.size.bytes.toNat := by
    rw [accessed.2];exact bounds
  have result := GeneralBorrowStructuralHistoryMutable.construct read.tree accessed.1 s.parentTag
    s.tracker.global.nextPointerTag s.data.input.parent s.data.input.parentNode parentTag parentNode fresh room
    s.offset s.len (UInt64.pos_iff_ne_zero.mp s.positive) afterBounds
  exact ⟨result.2.1,result.2.2.1.trans accessed.2,by rw [nodes] at result;exact result.2.2.2⟩
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowFinalState
