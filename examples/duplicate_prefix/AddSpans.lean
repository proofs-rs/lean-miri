import duplicate_prefix.AddLocals
import duplicate_prefix.MetadataSpans
namespace DuplicatePrefix.AddSpans
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
theorem local0_index :
    PreparedReflection.actual.program.bundle.spans.toList.idxOf? (AddLocals.localSpan ⟨0, by decide⟩) = some 615 := by
  refine SpanFacts.index_of_unique_key _ _ _ (by decide +kernel) ?_ ?_
  · with_unfolding_all rfl
  · decide +kernel

theorem local1_index :
    PreparedReflection.actual.program.bundle.spans.toList.idxOf? (AddLocals.localSpan ⟨1, by decide⟩) = some 616 := by
  refine SpanFacts.index_of_unique_key _ _ _ (by decide +kernel) ?_ ?_
  · with_unfolding_all rfl
  · decide +kernel

theorem local2_index :
    PreparedReflection.actual.program.bundle.spans.toList.idxOf? (AddLocals.localSpan ⟨2, by decide⟩) = some 617 := by
  refine SpanFacts.index_of_unique_key _ _ _ (by decide +kernel) ?_ ?_
  · with_unfolding_all rfl
  · decide +kernel

theorem local0_span
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee) :
    CompilerFrameContext.localSpan PreparedReflection.actual.compiler HelperCompilerFacts.addBody.body 0
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨615⟩ (Storage.withCurrent framesBefore frame machine) := by
  have valid : 0 < AddLocals.inputBody.input.locals.size := by decide +kernel
  let decl := AddLocals.inputBody.input.locals[0]'valid
  have present : AddLocals.inputBody.input.locals[0]? = some decl := by
    simp [decl, valid]
  have spanQuery : PreparedReflection.actual.compiler.program.bundle.spans.toList.idxOf?
      (AddLocals.localSpan ⟨0, by decide⟩) = some 615 := by
    rw [show PreparedReflection.actual.compiler.program = PreparedReflection.actual.program by rfl]
    exact local0_index
  exact MetadataSpans.local_span_from_metadata _ _ _ _ _ _ AddLocals.inputBody decl _ 615 body.symm
    (AddLocals.body_of_frame frame body identity callee) present rfl spanQuery

theorem local1_span
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee) :
    CompilerFrameContext.localSpan PreparedReflection.actual.compiler HelperCompilerFacts.addBody.body 1
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨616⟩ (Storage.withCurrent framesBefore frame machine) := by
  have valid : 1 < AddLocals.inputBody.input.locals.size := by decide +kernel
  let decl := AddLocals.inputBody.input.locals[1]'valid
  have present : AddLocals.inputBody.input.locals[1]? = some decl := by
    simp [decl, valid]
  have spanQuery : PreparedReflection.actual.compiler.program.bundle.spans.toList.idxOf?
      (AddLocals.localSpan ⟨1, by decide⟩) = some 616 := by
    rw [show PreparedReflection.actual.compiler.program = PreparedReflection.actual.program by rfl]
    exact local1_index
  exact MetadataSpans.local_span_from_metadata _ _ _ _ _ _ AddLocals.inputBody decl _ 616 body.symm
    (AddLocals.body_of_frame frame body identity callee) present rfl spanQuery

theorem local2_span
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee) :
    CompilerFrameContext.localSpan PreparedReflection.actual.compiler HelperCompilerFacts.addBody.body 2
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨617⟩ (Storage.withCurrent framesBefore frame machine) := by
  have valid : 2 < AddLocals.inputBody.input.locals.size := by decide +kernel
  let decl := AddLocals.inputBody.input.locals[2]'valid
  have present : AddLocals.inputBody.input.locals[2]? = some decl := by
    simp [decl, valid]
  have spanQuery : PreparedReflection.actual.compiler.program.bundle.spans.toList.idxOf?
      (AddLocals.localSpan ⟨2, by decide⟩) = some 617 := by
    rw [show PreparedReflection.actual.compiler.program = PreparedReflection.actual.program by rfl]
    exact local2_index
  exact MetadataSpans.local_span_from_metadata _ _ _ _ _ _ AddLocals.inputBody decl _ 617 body.symm
    (AddLocals.body_of_frame frame body identity callee) present rfl spanQuery

end
end DuplicatePrefix.AddSpans
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.AddSpans.local0_span, ``DuplicatePrefix.AddSpans.local1_span] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata span dependency {dependency}"
