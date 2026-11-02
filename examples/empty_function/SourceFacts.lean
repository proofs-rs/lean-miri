import empty_function.Program
import Miri.Input.CompilerConstantQueries
import Miri.Input.CompilerGlobals

/-! Closed facts checking the fixed metadata contract against the real fixture.
Preparation is reflected as safe constructor data, within the same explicitly
trusted compiler/import boundary as Program. This is not a safety proof. -/
namespace EmptyFunction.SourceFacts
open Lean Miri Miri.Input Miri.Interpreter Miri.MIR

/-- The fixed exported instruction requests Default-mode provenance resetting.
Requiring `.No` in the metadata contract would contradict this exact MIR. -/
theorem literal_retag_yes : ∃ destination literal,
    (Program.block.statements[0]'(by decide)).kind =
      .Assign destination (.Use (.Constant literal) .Yes) := by
  exact ⟨_, _, rfl⟩

deriving instance ToExpr for CompilerConstantQueries.PathElement
deriving instance ToExpr for Miri.MIR.Location
deriving instance ToExpr for CompilerConstantQueries.Site

private def prepareSites : IO (Except String (Array CompilerConstantQueries.Site)) := do
  let decoded ← Input.decodeFile "examples/empty_function/input.json"
  return do
    let decoded ← decoded
    let lowered ← Input.lowerProgram decoded.document
    let prepared ← CompilerConstantQueries.prepare (CompilerGlobals.prepareProgram lowered)
    pure (prepared.evidence.map (·.site))

open Lean Elab Command in
run_cmd do
  let result ← liftIO prepareSites
  let sites ← match result with
    | .ok value => pure value
    | .error reason => throwError "fixed empty_function compiler preparation failed: {reason}"
  liftCoreM <| addDecl <| .defnDecl {
    name := `EmptyFunction.SourceFacts.constantSites, levelParams := []
    type := mkApp (mkConst ``Array [0]) (mkConst ``CompilerConstantQueries.Site)
    value := toExpr sites, hints := .regular 0, safety := .safe }

theorem constant_envelope_site :
    constantSites[1]? = some ⟨Program.root.loaded.identity.index, ⟨0,0⟩,
      #[.field "kind", .field "rvalue", .field "operand", .field "constant"]⟩ := by rfl

open Lean Elab Command in
run_cmd do
  for name in #[``literal_retag_yes, ``constantSites, ``constant_envelope_site] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved fixed-source fact dependency {dependency}"

end EmptyFunction.SourceFacts
