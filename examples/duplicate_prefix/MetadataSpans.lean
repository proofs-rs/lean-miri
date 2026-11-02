import duplicate_prefix.MetadataLocals
namespace DuplicatePrefix.MetadataSpans
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
theorem local0_index :
    PreparedReflection.actual.program.bundle.spans.toList.idxOf? (MetadataLocals.localSpan ⟨0, by decide⟩) = some 634 := by
  refine SpanFacts.index_of_unique_key _ _ _ (by decide +kernel) ?_ ?_
  · with_unfolding_all rfl
  · decide +kernel

theorem local1_index :
    PreparedReflection.actual.program.bundle.spans.toList.idxOf? (MetadataLocals.localSpan ⟨1, by decide⟩) = some 635 := by
  refine SpanFacts.index_of_unique_key _ _ _ (by decide +kernel) ?_ ?_
  · with_unfolding_all rfl
  · decide +kernel

theorem local_span_from_metadata (compiler : CompilerProviders.Prepared)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (supplied : MIR.Body) (localId : Nat) (source : LoweredBody) (decl : Input.LocalDecl)
    (spanData : SourceSpanData) (index : Nat)
    (sameBody : supplied = frame.body)
    (sourceBody : CompilerFrameContext.bodyOfFrame compiler frame = .ok source)
    (sourceDecl : source.input.locals[localId]? = some decl)
    (declSpan : decl.sourceInfo.span = spanData)
    (lookupSpan : compiler.program.bundle.spans.toList.idxOf? spanData = some index) :
    CompilerFrameContext.localSpan compiler supplied localId (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨index⟩ (Storage.withCurrent framesBefore frame machine) := by
  unfold CompilerFrameContext.localSpan
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [sameBody]
  simp only [beq_self_eq_true, ite_true]
  rw [sourceBody]
  unfold_frame_query_lift
  simp only [EStateM.bind, pure, EStateM.pure]
  rw [sourceDecl]
  dsimp only
  rw [declSpan, lookupSpan]
  rfl

theorem local0_span
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee) :
    CompilerFrameContext.localSpan PreparedReflection.actual.compiler PtrMetadataHelper.body.body 0
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨634⟩ (Storage.withCurrent framesBefore frame machine) := by
  have valid : 0 < MetadataLocals.inputBody.input.locals.size := by decide +kernel
  let decl := MetadataLocals.inputBody.input.locals[0]'valid
  have present : MetadataLocals.inputBody.input.locals[0]? = some decl := by
    simp [decl, valid]
  have spanQuery : PreparedReflection.actual.compiler.program.bundle.spans.toList.idxOf?
      (MetadataLocals.localSpan ⟨0, by decide⟩) = some 634 := by
    rw [show PreparedReflection.actual.compiler.program = PreparedReflection.actual.program by rfl]
    exact local0_index
  exact local_span_from_metadata _ _ _ _ _ _ MetadataLocals.inputBody decl _ 634 body.symm
    (MetadataLocals.body_of_frame frame body identity callee) present rfl spanQuery

theorem local1_span
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState K User)
    (body : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee) :
    CompilerFrameContext.localSpan PreparedReflection.actual.compiler PtrMetadataHelper.body.body 1
      (Storage.withCurrent framesBefore frame machine) =
      .ok ⟨635⟩ (Storage.withCurrent framesBefore frame machine) := by
  have valid : 1 < MetadataLocals.inputBody.input.locals.size := by decide +kernel
  let decl := MetadataLocals.inputBody.input.locals[1]'valid
  have present : MetadataLocals.inputBody.input.locals[1]? = some decl := by
    simp [decl, valid]
  have spanQuery : PreparedReflection.actual.compiler.program.bundle.spans.toList.idxOf?
      (MetadataLocals.localSpan ⟨1, by decide⟩) = some 635 := by
    rw [show PreparedReflection.actual.compiler.program = PreparedReflection.actual.program by rfl]
    exact local1_index
  exact local_span_from_metadata _ _ _ _ _ _ MetadataLocals.inputBody decl _ 635 body.symm
    (MetadataLocals.body_of_frame frame body identity callee) present rfl spanQuery

end
end DuplicatePrefix.MetadataSpans
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.MetadataSpans.local0_span, ``DuplicatePrefix.MetadataSpans.local1_span] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata span dependency {dependency}"
