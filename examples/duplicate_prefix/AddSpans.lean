import duplicate_prefix.AddLocals
import duplicate_prefix.MetadataSpans
namespace DuplicatePrefix.AddSpans
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
theorem local0_index :
    PreparedReflection.actual.program.bundle.spans.toList.idxOf? (AddLocals.localSpan ⟨0, by decide⟩) = some 80 := by
  refine SpanFacts.index_of_unique_key _ _ _ (by decide +kernel) ?_ ?_
  · with_unfolding_all rfl
  · decide +kernel

theorem local1_index :
    PreparedReflection.actual.program.bundle.spans.toList.idxOf? (AddLocals.localSpan ⟨1, by decide⟩) = some 81 := by
  refine SpanFacts.index_of_unique_key _ _ _ (by decide +kernel) ?_ ?_
  · with_unfolding_all rfl
  · decide +kernel

theorem local2_index :
    PreparedReflection.actual.program.bundle.spans.toList.idxOf? (AddLocals.localSpan ⟨2, by decide⟩) = some 82 := by
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
      .ok ⟨80⟩ (Storage.withCurrent framesBefore frame machine) := by
  have valid : 0 < AddLocals.inputBody.input.localSources.size := by decide +kernel
  let decl := AddLocals.inputBody.input.localSources[0]'valid
  have present : AddLocals.inputBody.input.localSources[0]? = some decl := by
    simp [decl, valid]
  have spanQuery : PreparedReflection.actual.compiler.program.bundle.spans.toList.idxOf?
      (AddLocals.localSpan ⟨0, by decide⟩) = some 80 := by
    rw [show PreparedReflection.actual.compiler.program = PreparedReflection.actual.program by rfl]
    exact local0_index
  exact MetadataSpans.local_span_from_metadata _ _ _ _ _ _ AddLocals.inputBody decl 80 body.symm
    (AddLocals.body_of_frame frame body identity callee) present (by with_unfolding_all rfl) (by decide +kernel)

theorem local1_span
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee) :
    CompilerFrameContext.localSpan PreparedReflection.actual.compiler HelperCompilerFacts.addBody.body 1
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨81⟩ (Storage.withCurrent framesBefore frame machine) := by
  have valid : 1 < AddLocals.inputBody.input.localSources.size := by decide +kernel
  let decl := AddLocals.inputBody.input.localSources[1]'valid
  have present : AddLocals.inputBody.input.localSources[1]? = some decl := by
    simp [decl, valid]
  have spanQuery : PreparedReflection.actual.compiler.program.bundle.spans.toList.idxOf?
      (AddLocals.localSpan ⟨1, by decide⟩) = some 81 := by
    rw [show PreparedReflection.actual.compiler.program = PreparedReflection.actual.program by rfl]
    exact local1_index
  exact MetadataSpans.local_span_from_metadata _ _ _ _ _ _ AddLocals.inputBody decl 81 body.symm
    (AddLocals.body_of_frame frame body identity callee) present (by with_unfolding_all rfl) (by decide +kernel)

theorem local2_span
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee) :
    CompilerFrameContext.localSpan PreparedReflection.actual.compiler HelperCompilerFacts.addBody.body 2
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨82⟩ (Storage.withCurrent framesBefore frame machine) := by
  have valid : 2 < AddLocals.inputBody.input.localSources.size := by decide +kernel
  let decl := AddLocals.inputBody.input.localSources[2]'valid
  have present : AddLocals.inputBody.input.localSources[2]? = some decl := by
    simp [decl, valid]
  have spanQuery : PreparedReflection.actual.compiler.program.bundle.spans.toList.idxOf?
      (AddLocals.localSpan ⟨2, by decide⟩) = some 82 := by
    rw [show PreparedReflection.actual.compiler.program = PreparedReflection.actual.program by rfl]
    exact local2_index
  exact MetadataSpans.local_span_from_metadata _ _ _ _ _ _ AddLocals.inputBody decl 82 body.symm
    (AddLocals.body_of_frame frame body identity callee) present (by with_unfolding_all rfl) (by decide +kernel)

end
end DuplicatePrefix.AddSpans
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.AddSpans.local0_span, ``DuplicatePrefix.AddSpans.local1_span] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata span dependency {dependency}"
