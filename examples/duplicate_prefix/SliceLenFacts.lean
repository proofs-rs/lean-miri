import duplicate_prefix.PtrMetadataComplete
import duplicate_prefix.SharedReferenceMetadata
namespace DuplicatePrefix.SliceLenFacts
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

def body := HelperCompilerFacts.lenBody

theorem body_shape : (body.body.argumentCount,body.body.locals,body.body.basicBlocks.size) = (1,#[5,7,154],2) := by decide +kernel

theorem statements :
    CopyPreconditions.Bodies.statementKindAt body.body 0 0 = some (.StorageLive 2) ∧
    CopyPreconditions.Bodies.statementKindAt body.body 0 1 = some (.Assign ⟨2,#[]⟩ (.RawPtr .Const ⟨1,#[.Deref]⟩)) ∧
    CopyPreconditions.Bodies.statementKindAt body.body 1 0 = some (.StorageDead 2) ∧
    CopyPreconditions.Bodies.terminatorKindAt body.body 1 = some .Return := by exact ⟨rfl,rfl,rfl,rfl⟩

def callTerminator := (body.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)).terminator

theorem call_shape :
    match callTerminator.kind with
    | .Call function arguments destination target unwind _ _ =>
      function = PtrMetadataHelper.resolved.function ∧
      arguments.map (·.operand) = #[.Move ⟨2,#[]⟩] ∧ destination = ⟨0,#[]⟩ ∧
      target = some 1 ∧ unwind = .Continue
    | _ => False := by
  refine ⟨rfl,?_,rfl,rfl,rfl⟩
  decide +kernel

theorem normalized_local2 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = body.body) (identity : frame.bodyIdentity = body.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.lenCall.callee) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 2 = .ok 154 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem raw_type_shape : CompilerFacts.retagTypeShape RootMetadataQueries.context 154 =
    .ok {isReference := false,isRawPointer := true} := by
  unfold CompilerFacts.retagTypeShape CompilerFacts.boolean
  unfold_fact_helpers
  simp only [RootMetadataQueries.context_node]
  decide +kernel

#print axioms statements
#print axioms normalized_local2
#print axioms raw_type_shape
end
end DuplicatePrefix.SliceLenFacts
