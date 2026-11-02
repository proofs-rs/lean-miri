import duplicate_prefix.PointerAddFacts
import duplicate_prefix.CopyHelperUnit
import duplicate_prefix.CopyPreconditions
namespace DuplicatePrefix.CopyHelperFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem normalized_local0 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 0 = .ok 2 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem normalized_local4 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 4 = .ok 2 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem normalized_local5 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 5 = .ok 0 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem normalized_local14 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 14 = .ok 9 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem normalized_local15 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 15 = .ok 8 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem normalized_local16 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 16 = .ok 5 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem actual_unit_query (framesBefore : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 4
      (Storage.withCurrent framesBefore frame machine) =
    .ok CopyHelperUnit.layout (Storage.withCurrent framesBefore frame machine) :=
  PointerAddFacts.compute_local framesBefore frame machine 4 2 CopyHelperUnit.layout
    (normalized_local4 frame sourceBody identity callee) CopyHelperUnit.layout_query

theorem copy_intrinsic_statement : CopyPreconditions.Bodies.statementKindAt HelperCompilerFacts.copyBody.body 7 8 =
    some (.Intrinsic (.CopyNonOverlapping ⟨.Move ⟨14,#[]⟩, .Move ⟨15,#[]⟩, .Move ⟨16,#[]⟩⟩)) := by decide +kernel

theorem source_copy_statement : CopyPreconditions.Bodies.statementKindAt HelperCompilerFacts.copyBody.body 7 3 =
    some (.Assign ⟨14,#[]⟩ (.Use (.Copy ⟨1,#[]⟩) .Yes)) := by decide +kernel

theorem destination_copy_statement : CopyPreconditions.Bodies.statementKindAt HelperCompilerFacts.copyBody.body 7 5 =
    some (.Assign ⟨15,#[]⟩ (.Use (.Copy ⟨2,#[]⟩) .Yes)) := by decide +kernel

theorem count_copy_statement : CopyPreconditions.Bodies.statementKindAt HelperCompilerFacts.copyBody.body 7 7 =
    some (.Assign ⟨16,#[]⟩ (.Use (.Copy ⟨3,#[]⟩) .Yes)) := by decide +kernel

#print axioms actual_unit_query
open Lean Elab Command in
run_cmd do
  for declaration in [``normalized_local0, ``normalized_local4, ``normalized_local5,
      ``normalized_local14, ``normalized_local15, ``normalized_local16, ``actual_unit_query] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperFacts
