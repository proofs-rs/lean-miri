import duplicate_prefix.AsMutPush
import duplicate_prefix.AsMutPtrArgumentCopy
namespace DuplicatePrefix.AsMutLocals
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def inputBody : LoweredBody := PreparedReflection.actual.program.bundle.bodies[HelperCompilerFacts.asMutPtrBody.identity.index]'(by decide +kernel)
def localSpan (id : Fin 5) : SourceSpanData :=
  (inputBody.input.locals[id.val]'(by
    have size : inputBody.input.locals.size = 5 := by rfl
    omega)).sourceInfo.span
def spanQuery (id : Fin 5) := PreparedReflection.actual.program.bundle.spans.toList.idxOf? (localSpan id)
theorem body_of_frame (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee) :
    CompilerFrameContext.bodyOfFrame PreparedReflection.actual.compiler frame = .ok inputBody := by
  unfold CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

theorem normalized_local1 (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 1 = .ok 3 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

theorem compute_local1
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 1
      (Storage.withCurrent frames frame machine) =
      .ok ActualReferenceMetadata.reference (Storage.withCurrent frames frame machine) := by
  have normalized := normalized_local1 frame body identity callee
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [normalized]
  with_unfolding_all change (match PreparedReflection.actual.runtime.lookup 3 with
    | .ok value => EStateM.Result.ok value (Storage.withCurrent frames frame machine)
    | .error error => EStateM.Result.error (StepError.unsupported s!"compiler frame query: {toString error}")
        (Storage.withCurrent frames frame machine)) = _
  rw [RootCompilerFacts.slice_layout_eq]
  rfl
end
end DuplicatePrefix.AsMutLocals

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.AsMutLocals.body_of_frame, ``DuplicatePrefix.AsMutLocals.normalized_local1, ``DuplicatePrefix.AsMutLocals.compute_local1] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata local dependency {dependency}"
