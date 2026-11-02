import duplicate_prefix.GeneralBorrowProtectedSiblingFunctionInput
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowProtectedSiblingFunctionCaller GeneralBorrowProtectedSiblingFunctionHistory
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

/-- A real positive-capacity allocation, arbitrary finite simultaneously held
protected siblings without exposure, every source release, and actual endCall
form the original function's all-count borrow input. Only physical caller,
MIR/compiler, memory initialization and finite numeric resources are supplied.
The original call initializes its frame, follows the physical zero/accepted/
rejected branch, returns with an empty stack and has no UB on any permitted
finite prefix. This is the specified source protocol, not arbitrary Rust history. -/
theorem invoke (bytes : UInt64) (nonzero : bytes ≠ 0) (n : Nat) (room : n+10 ≤ 4294967295)
    (s : Caller (generate bytes nonzero n room).output.tree (generate bytes nonzero n room).output.ended bytes) :
    GeneralBorrowProtectedSiblingWindowLifetimes.operation bytes (List.replicate n false) = .ok (generate bytes nonzero n room).output ∧
      GeneralBorrowForestAllCountSafety.Result
        (GeneralBorrowProtectedSiblingFunctionInput.assemble nonzero room (generate bytes nonzero n room) s) := by
  exact ⟨(generate bytes nonzero n room).actual,GeneralBorrowForestAllCountSafety.invoke _⟩
end
end DuplicatePrefix.GeneralBorrowProtectedSiblingFunctionSafety
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GeneralBorrowProtectedSiblingFunctionSafety.invoke] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved generated sibling original invocation dependency {dependency}"
