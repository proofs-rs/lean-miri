import duplicate_prefix.GeneralBorrowPositiveWildcardWindowOriginalInput
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowArgumentCopy
import duplicate_prefix.GeneralBorrowStructuralHistoryWildcard
import duplicate_prefix.GeneralBorrowSparseExposedLeafRange
import duplicate_prefix.GeneralBorrowFreshReadFrame
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowFinalState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.DataStructures
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
/-- The actual window wildcard Read followed by protected FnEntry construction
retains intrinsic State, exact byte capacity and bounded node growth. -/
theorem build (s : GeneralBorrowPositiveWildcardWindowOriginalInput.Base) :
    let after := GeneralBorrowPositiveWildcardWindowArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.offset s.len
    GeneralBorrowStructuralHistoryState.State after ∧ after.locations.size=s.entry.allocation.extra.locations.size ∧
      after.nodes.size≤s.entry.allocation.extra.nodes.size+1 := by
  let tree:=s.entry.allocation.extra
  let protections := (TypedBorrowSteps.registeredGlobal s.tracker s.tracker.global.nextPointerTag).protectedTags
  let read:=tree.performBorrowAccessRange .wildcard (Size.ofBytes s.offset) (Size.ofBytes s.len) .Read protections .VisitChildrenOfAccessed
  have bounds : s.offset.toNat+s.len.toNat≤tree.locations.size.bytes.toNat := by rw [s.allocationCapacity];exact s.bounds
  have owned : GeneralRangeMapOrigins.OwnedOn (fun location=>GeneralBorrowSparseExposedLeafState.Raw tree location protections) s.offset (s.offset+s.len) tree.locations := by
    intro position valid _ _ _;exact s.sourceRaw position valid
  have result:=GeneralBorrowSparseExposedLeafRange.access tree protections s.head s.extraRoots s.leafGeometry (Size.ofBytes s.offset) (Size.ofBytes s.len)
    .Read .VisitChildrenOfAccessed s.initialState.well s.offset (s.offset+s.len) owned bounds (Nat.le_refl _) (Nat.le_refl _)
  have capacity : read.tree.locations.size=tree.locations.size := result.2.2.2
  have frame : read.tree={tree with locations:=read.tree.locations} := GeneralBorrowFreshReadFrame.frame tree .wildcard (Size.ofBytes s.offset)
    (Size.ofBytes s.len) .Read protections .VisitChildrenOfAccessed
  have state : GeneralBorrowStructuralHistoryState.State read.tree := by
    rw [frame]
    exact ⟨GeneralBorrowStructuralHistoryState.graph_locations tree read.tree.locations s.initialState.toGraphState,result.2.2.1⟩
  have mapping : read.tree.tagMapping=tree.tagMapping := by simpa only using congrArg BorrowTree.tagMapping frame
  have nodes : read.tree.nodes=tree.nodes := by simpa only using congrArg BorrowTree.nodes frame
  have fresh : GeneralBorrowTagMap.Fresh read.tree.tagMapping s.tracker.global.nextPointerTag := by rw [mapping];exact s.tagFresh
  have free : read.tree.tagMapping.deassigned.back?=none := by rw [mapping];exact s.noFree
  have fits : read.tree.tagMapping.mapping.size≤4294967295 := by rw [mapping];exact s.fits
  have nextBounds : s.offset.toNat+s.len.toNat≤read.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have room : read.tree.nodes.size+1≤4294967295 := by rw [nodes];change s.entry.allocation.extra.nodes.size+1≤4294967295;have h:=s.nodeRoom;omega
  have actual:=GeneralBorrowPositiveWildcardConstructor.append read.tree s.tracker.global.nextPointerTag fresh free fits
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl s.offset s.len (UInt64.pos_iff_ne_zero.mp s.positive) result.2.2.1 nextBounds
  have structural:=GeneralBorrowStructuralHistoryWildcard.construct read.tree state s.tracker.global.nextPointerTag fresh room s.offset s.len nextBounds
  dsimp only at structural
  rw [actual] at structural
  rw [mapping] at structural
  exact ⟨structural.2.1,structural.2.2.1.trans capacity,by rw [nodes] at structural;exact structural.2.2.2⟩
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowFinalState
