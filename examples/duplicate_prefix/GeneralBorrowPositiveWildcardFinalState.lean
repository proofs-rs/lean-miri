import duplicate_prefix.GeneralBorrowPositiveWildcardArgumentCopy
import duplicate_prefix.GeneralBorrowStructuralHistoryWildcard
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardFinalState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.DataStructures
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- The actual wildcard argument's exact final tree retains all structural
allocator certificates and partition geometry, from the original caller State. -/
theorem build (tree : BorrowTree) (initial : GeneralBorrowStructuralHistoryState.State tree)
    (tracker : MachineHooks.BorrowState) (len : UInt64) (positive : len≠0)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tracker.global.nextPointerTag)
    (noFree : tree.tagMapping.deassigned.back?=none) (fits : tree.tagMapping.mapping.size≤4294967295)
    (room : tree.nodes.size+1≤4294967295)
    (bounds : (0 : UInt64).toNat+len.toNat≤tree.locations.size.bytes.toNat) :
    let after := GeneralBorrowPositiveWildcardArgumentCopy.finalTree tree tracker len
    GeneralBorrowStructuralHistoryState.State after ∧ after.locations.size=tree.locations.size ∧ after.nodes.size≤tree.nodes.size+1 := by
  have actual := GeneralBorrowPositiveWildcardConstructor.append tree tracker.global.nextPointerTag fresh noFree fits
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl 0 len positive initial.well bounds
  have structural := GeneralBorrowStructuralHistoryWildcard.construct tree initial tracker.global.nextPointerTag fresh room 0 len bounds
  dsimp only at structural
  rw [actual] at structural
  exact structural.2
end DuplicatePrefix.GeneralBorrowPositiveWildcardFinalState
