import duplicate_prefix.GeneralBorrowProtectedSiblingPartialFunctionInput
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingPartialFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowProtectedSiblingFunctionCaller GeneralBorrowProtectedSiblingPartialFunctionHistory
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section

/-- A real positive-capacity allocation, arbitrary finite chronologically
ordered positive partial/overlapping protected siblings without exposure, every
source release, and actual endCall
form the original function's all-count borrow input. Only physical caller,
MIR/compiler, memory initialization and finite numeric resources are supplied.
The original call initializes its frame, follows the physical zero/accepted/
rejected branch, returns with an empty stack and has no UB on any permitted
finite prefix. This is the specified source protocol, not arbitrary Rust history. -/
theorem invoke (bytes : UInt64) (nonzero : bytes ≠ 0) (windows : List (GeneralBorrowProtectedSiblingPartial.Window bytes)) (room : windows.length+10 ≤ 4294967295)
    (s : Caller (generate bytes nonzero windows room).output.tree (generate bytes nonzero windows room).output.ended bytes) :
    GeneralBorrowProtectedSiblingPartialFunctionHistory.operation bytes windows = .ok (generate bytes nonzero windows room).output ∧
      GeneralBorrowForestAllCountSafety.Result
        (GeneralBorrowProtectedSiblingPartialFunctionInput.assemble nonzero room (generate bytes nonzero windows room) s) := by
  exact ⟨(generate bytes nonzero windows room).actual,GeneralBorrowForestAllCountSafety.invoke _⟩
end
end DuplicatePrefix.GeneralBorrowProtectedSiblingPartialFunctionSafety
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GeneralBorrowProtectedSiblingPartialFunctionSafety.invoke] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved generated sibling original invocation dependency {dependency}"
