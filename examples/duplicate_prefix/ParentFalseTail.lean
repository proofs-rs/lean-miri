import duplicate_prefix.ParentFalseAssignment
import duplicate_prefix.ParentFalseReturn
import duplicate_prefix.CanonicalConfigFacts

/-! The source-level storage dead at the end of the false branch. -/
namespace DuplicatePrefix.ParentFalseTail
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open DuplicatePrefix

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem storage_dead_one_statement :
    ∃ block statement,
      CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[4]? = some block ∧
      block.statements[0]? = some statement ∧ statement.kind = .StorageDead 1 := by
  have shape : CopyPreconditions.Bodies.statementKindAt
      CopyPreconditions.Bodies.checkLanguage.loaded.body 4 0 = some (.StorageDead 1) := by
    with_unfolding_all rfl
  cases blockEq : CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[4]? with
  | none => simp [CopyPreconditions.Bodies.statementKindAt,blockEq] at shape
  | some block =>
    cases statementEq : block.statements[0]? with
    | none => simp [CopyPreconditions.Bodies.statementKindAt,blockEq,statementEq] at shape
    | some statement =>
      refine ⟨block,statement,rfl,statementEq,?_⟩
      simpa [CopyPreconditions.Bodies.statementKindAt,blockEq,statementEq] using shape

theorem storage_dead_one_step [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (location : frame.location = .mir ⟨4,0⟩)
    (valid1 : (1 : MIR.LocalId) < frame.locals.size)
    (live1 : frame.locals[1].value = .live (.immediate (.scalar (.fromBool false)))) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
    (Storage.withCurrent frames
        (SourceSteps.deadFrame frame ⟨4,0⟩ 1 valid1) machine,.ok true) := by
  obtain ⟨block,statement,blockAt,statementAt,kind⟩ := storage_dead_one_statement
  have blockAt' : frame.body.basicBlocks[4]? = some block := by rw [body]; exact blockAt
  exact SourceSteps.storage_dead_exact (PreparedContracts.actualConfig options () (remaining+1) span)
    limits () frames frame machine ⟨4,0⟩ block statement 1 (.scalar (.fromBool false)) location blockAt'
    statementAt kind valid1 (by decide) live1


#print axioms storage_dead_one_statement
#print axioms storage_dead_one_step

end DuplicatePrefix.ParentFalseTail

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ParentFalseTail.storage_dead_one_statement,
      ``DuplicatePrefix.ParentFalseTail.storage_dead_one_step] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError s!"unapproved parent false-tail dependency {dependency}"
