import empty_function.Program
import Miri.Input.CompilerConstantQueries
import Miri.Input.CompilerGlobals

/-! Closed facts checking the fixed metadata contract against the real fixture.
Preparation is reflected as safe constructor data, within the same explicitly
trusted compiler/import boundary as Program. This is not a safety proof. -/
namespace EmptyFunction.SourceFacts
open Lean Miri Miri.Input Miri.Interpreter Miri.MIR
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The fixed exported instruction requests Default-mode provenance resetting.
Requiring `.No` in the metadata contract would contradict this exact MIR. -/
theorem literal_retag_yes : ∃ destination literal,
    ((Program.contents.basicBlocks[0]'(by with_unfolding_all decide)).statements[0]'(by with_unfolding_all decide)).kind =
      .Assign destination (.Use (.Constant literal) .Yes) := by
  with_unfolding_all exact ⟨_, _, rfl⟩

deriving instance ToExpr for CompilerConstantQueries.Site

private def prepareSites : IO (Except String (Array CompilerConstantQueries.Site)) := do
  let decoded ← Input.decodeFile "examples/empty_function/input.json"
  return do
    let decoded ← decoded
    let lowered ← Input.lowerProgram decoded.document
    let owner ← RuntimeProgram.ofProgram (CompilerGlobals.prepareProgram lowered)
    let prepared ← CompilerConstantQueries.prepare owner
    let mut sites := #[]
    for bodyIndex in [:prepared.bodies.size] do
      if let some (.ok table) := prepared.bodies[bodyIndex]? then
        for constantIndex in [:table.size] do
          if let some (some (.ok _)) := table[constantIndex]? then
            sites := sites.push (⟨bodyIndex,⟨constantIndex⟩⟩ : CompilerConstantQueries.Site)
    pure sites

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
    ∃ (index : Nat) (id : ConstantId),
      constantSites[index]? = some (⟨Program.root.loaded.identity.index,id⟩ : CompilerConstantQueries.Site) ∧
      Meaning.firstConstantId Program.root.loaded.tables Program.root.loaded.body = .ok id := by
  with_unfolding_all exact ⟨1,_,rfl,rfl⟩

open Lean Elab Command in
run_cmd do
  for name in #[``literal_retag_yes, ``constantSites, ``constant_envelope_site] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved fixed-source fact dependency {dependency}"

end EmptyFunction.SourceFacts
