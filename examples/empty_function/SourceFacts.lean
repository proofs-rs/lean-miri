import empty_function.Program

/-! Closed facts checking the fixed metadata contract against the real fixture.
The resolved instruction is checked within the same explicitly trusted
compiler/import boundary as Program. This is not a safety proof. -/
namespace EmptyFunction.SourceFacts
open Lean Miri Miri.Input Miri.Interpreter Miri.MIR

/-- The fixed exported instruction requests Default-mode provenance resetting.
Requiring `.No` in the metadata contract would contradict this exact MIR. -/
theorem literal_retag_yes : ∃ destination literal,
    (Program.block.statements[0]'(by decide)).kind =
      .Assign destination (.Use (.Constant literal) .Yes) := by
  exact ⟨_, _, rfl⟩

open Lean Elab Command in
run_cmd do
  for name in #[``literal_retag_yes] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved fixed-source fact dependency {dependency}"

end EmptyFunction.SourceFacts
