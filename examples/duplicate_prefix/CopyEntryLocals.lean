import duplicate_prefix.CopyFrameData
import duplicate_prefix.CopyArgumentStage
import duplicate_prefix.MetadataSpans
namespace DuplicatePrefix.CopyEntryLocals
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable def inputBody : LoweredBody :=
  PreparedReflection.actual.program.bundle.bodies[HelperCompilerFacts.copyBody.identity.index]'(by decide +kernel)
noncomputable def localSpan (index : Fin 17) :=
  (inputBody.input.locals[index.val]'(by
    have size : inputBody.input.locals.size = 17 := by rfl
    rw [size]
    exact index.isLt)).sourceInfo.span
 theorem body_of_frame (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) :
    CompilerFrameContext.bodyOfFrame PreparedReflection.actual.compiler frame = .ok inputBody := by
  unfold CompilerFrameContext.bodyOfFrame
  rw [body,identity,callee]
  with_unfolding_all rfl
 theorem normalized_argument (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) (index : Fin 3) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame (index.val+1) =
      .ok (CopyArgumentStage.layout index).ty := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body,identity,callee]
  rcases CopyArgumentStage.cases_three index with rfl | rfl | rfl <;> with_unfolding_all rfl
 theorem runtime_argument (index : Fin 3) :
    PreparedReflection.actual.runtime.lookup (CopyArgumentStage.layout index).ty = .ok (CopyArgumentStage.layout index) := by
  rcases CopyArgumentStage.cases_three index with rfl | rfl | rfl
  · exact CopyCompilerFacts.source_pointer_layout_eq
  · exact CopyCompilerFacts.dest_pointer_layout_eq
  · exact RootCompilerFacts.usize_layout_eq
 theorem compute_argument
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) (index : Fin 3) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler (index.val+1)
      (Storage.withCurrent frames frame machine) =
      .ok (CopyArgumentStage.layout index) (Storage.withCurrent frames frame machine) := by
  have normalized := normalized_argument frame body identity callee index
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [normalized]
  unfold_frame_query_lift
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  have query : PreparedReflection.actual.compiler.runtime.lookup (CopyArgumentStage.layout index).ty =
      .ok (CopyArgumentStage.layout index) := runtime_argument index
  rw [query]
  rfl

end
end DuplicatePrefix.CopyEntryLocals
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.CopyEntryLocals.body_of_frame, ``DuplicatePrefix.CopyEntryLocals.normalized_argument,
      ``DuplicatePrefix.CopyEntryLocals.compute_argument] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved copy entry locals {dependency}"
