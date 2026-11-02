import duplicate_prefix.AsMutLocals
import duplicate_prefix.MetadataSpans
namespace DuplicatePrefix.AsMutSpans
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
theorem local0_index :
    PreparedReflection.actual.program.bundle.spans.toList.idxOf? (AsMutLocals.localSpan ⟨0, by decide⟩) = some 612 := by
  refine SpanFacts.index_of_unique_key _ _ _ (by decide +kernel) ?_ ?_
  · with_unfolding_all rfl
  · decide +kernel

theorem local1_index :
    PreparedReflection.actual.program.bundle.spans.toList.idxOf? (AsMutLocals.localSpan ⟨1, by decide⟩) = some 613 := by
  refine SpanFacts.index_of_unique_key _ _ _ (by decide +kernel) ?_ ?_
  · with_unfolding_all rfl
  · decide +kernel

theorem local0_span
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee) :
    CompilerFrameContext.localSpan PreparedReflection.actual.compiler HelperCompilerFacts.asMutPtrBody.body 0
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨612⟩ (Storage.withCurrent framesBefore frame machine) := by
  have valid : 0 < AsMutLocals.inputBody.input.locals.size := by decide +kernel
  let decl := AsMutLocals.inputBody.input.locals[0]'valid
  have present : AsMutLocals.inputBody.input.locals[0]? = some decl := by
    simp [decl, valid]
  have spanQuery : PreparedReflection.actual.compiler.program.bundle.spans.toList.idxOf?
      (AsMutLocals.localSpan ⟨0, by decide⟩) = some 612 := by
    rw [show PreparedReflection.actual.compiler.program = PreparedReflection.actual.program by rfl]
    exact local0_index
  exact MetadataSpans.local_span_from_metadata _ _ _ _ _ _ AsMutLocals.inputBody decl _ 612 body.symm
    (AsMutLocals.body_of_frame frame body identity callee) present rfl spanQuery

theorem local1_span
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee) :
    CompilerFrameContext.localSpan PreparedReflection.actual.compiler HelperCompilerFacts.asMutPtrBody.body 1
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨613⟩ (Storage.withCurrent framesBefore frame machine) := by
  have valid : 1 < AsMutLocals.inputBody.input.locals.size := by decide +kernel
  let decl := AsMutLocals.inputBody.input.locals[1]'valid
  have present : AsMutLocals.inputBody.input.locals[1]? = some decl := by
    simp [decl, valid]
  have spanQuery : PreparedReflection.actual.compiler.program.bundle.spans.toList.idxOf?
      (AsMutLocals.localSpan ⟨1, by decide⟩) = some 613 := by
    rw [show PreparedReflection.actual.compiler.program = PreparedReflection.actual.program by rfl]
    exact local1_index
  exact MetadataSpans.local_span_from_metadata _ _ _ _ _ _ AsMutLocals.inputBody decl _ 613 body.symm
    (AsMutLocals.body_of_frame frame body identity callee) present rfl spanQuery

end
end DuplicatePrefix.AsMutSpans
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.AsMutSpans.local0_span, ``DuplicatePrefix.AsMutSpans.local1_span] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata span dependency {dependency}"
