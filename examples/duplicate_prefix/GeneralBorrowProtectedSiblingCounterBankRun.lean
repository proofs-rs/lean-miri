import duplicate_prefix.GeneralBorrowProtectedSiblingCounterBankPlan
import duplicate_prefix.GeneralBorrowProtectedSiblingCounterBankSplit
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBankRun
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingCounterBank
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- Source steps are genuinely interleaved on one global and one bank state.
Every step's singleton allocation trace and actual bank transition share their
returned action/tag; the very same outputs feed the next chronological step. -/
inductive Run {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (positive : len ≠ 0) (terminal : BorTag) : GlobalState →
      GeneralBorrowSharedRootBankState.State root rootTag offset len → List Instruction → GlobalState →
      GeneralBorrowSharedRootBankState.State root rootTag offset len → Prop where
  | nil (global state) : Run positive terminal global state [] global state
  | step {global advanced finalGlobal initial middle finalState instruction action rest}
      (allocation : Allocation global [instruction] [action] advanced)
      (protections : global.protectedTags = {})
      (actual : GeneralBorrowSharedBankMutableHistory.Run positive terminal initial [action] middle)
      (tail : Run positive terminal advanced middle rest finalGlobal finalState) :
      Run positive terminal global initial (instruction::rest) finalGlobal finalState

/-- Joining aligned traces produces an interleaved source history, not two
independent executions or a union of accepted input families. -/
theorem interleave {root rootTag offset len} {positive : len ≠ 0} {terminal : BorTag}
    {global finalGlobal instructions actions}
    (allocation : Allocation global instructions actions finalGlobal)
    {initial final : GeneralBorrowSharedRootBankState.State root rootTag offset len}
    (actual : GeneralBorrowSharedBankMutableHistory.Run positive terminal initial actions final)
    (empty : global.protectedTags = {}) :
    Run positive terminal global initial instructions finalGlobal final := by
  induction allocation generalizing initial final with
  | nil global => cases actual;exact .nil _ _
  | @borrow global advanced finalGlobal tag position rest actions allocated tail ih =>
    obtain ⟨middle,one,later⟩ := GeneralBorrowProtectedSiblingCounterBankSplit.first actual
    exact .step (.borrow allocated (.nil _)) empty one
      (ih later ((GeneralBorrowProtectedSiblingWindowTable.allocated global advanced tag allocated).trans empty))
  | @mutable global advanced finalGlobal tag rest actions allocated tail ih =>
    obtain ⟨middle,one,later⟩ := GeneralBorrowProtectedSiblingCounterBankSplit.first actual
    exact .step (.mutable allocated (.nil _)) empty one
      (ih later ((GeneralBorrowProtectedSiblingWindowTable.allocated global advanced tag allocated).trans empty))
  | gc tail ih =>
    obtain ⟨middle,one,later⟩ := GeneralBorrowProtectedSiblingCounterBankSplit.first actual
    exact .step (.gc (.nil _)) empty one (ih later empty)
  | exposeRoot tail ih =>
    obtain ⟨middle,one,later⟩ := GeneralBorrowProtectedSiblingCounterBankSplit.first actual
    exact .step (.exposeRoot (.nil _)) empty one (ih later empty)
  | rootAccess tail ih =>
    obtain ⟨middle,one,later⟩ := GeneralBorrowProtectedSiblingCounterBankSplit.first actual
    exact .step (.rootAccess (.nil _)) empty one (ih later empty)
end DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBankRun
