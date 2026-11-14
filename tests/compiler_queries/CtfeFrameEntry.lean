import Miri.Interpreter.CompileTime.FrameEntry

/-! Kernel-checked control examples. These callbacks record abstract requests;
they do not stand in for compiler normalization or CTFE query evaluation. -/
namespace CtfeFrameEntryTests
open Miri.Interpreter.CompileTime.FrameEntry
private def request (_pending : Nat) (source : Nat) : Action (List Nat) String Unit :=
  fun world => (.ok (),world ++ [source])
private def finish (pending : Nat) : Action (List Nat) String Nat :=
  fun world => (.ok pending,world ++ [99])
private def rejectEight (_pending : Nat) (source : Nat) : Action (List Nat) String Unit :=
  fun world => (if source == 8 then .error "query error" else .ok (),world ++ [source])
private def rejectFinish (_pending : Nat) : Action (List Nat) String Nat :=
  fun world => (.error "initialization error",world ++ [99])

theorem orderedDuplicates : enter #[7,7] request finish 13 [] =
    .ready 13 [7,7,99] 2 := rfl
theorem failurePreservesWorldAndPending : enter #[7,8,9] rejectEight finish 13 [] =
    .failed "query error" (.requiredConstant 1) 13 [7,8] 1 := rfl
theorem firstFailurePrecedesInitialization : enter #[8,7] rejectEight finish 13 [] =
    .failed "query error" (.requiredConstant 0) 13 [8] 0 := rfl
theorem initializationFailurePreservesWorld : enter #[7,7] request rejectFinish 13 [] =
    .failed "initialization error" .initialization 13 [7,7,99] 2 := rfl
theorem emptyDomainStillInitializes : enter #[] request finish 13 [] =
    .ready 13 [99] 0 := rfl

#print axioms orderedDuplicates
#print axioms failurePreservesWorldAndPending
#print axioms firstFailurePrecedesInitialization
#print axioms initializationFailurePreservesWorld
#print axioms emptyDomainStillInitializes
end CtfeFrameEntryTests
