import duplicate_prefix.HelperCompilerFacts
import duplicate_prefix.ActualOffset
import duplicate_prefix.ActualLocalPlace

namespace DuplicatePrefix.PointerAddFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem normalized_local0 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 0 = .ok 8 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem normalized_local3 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 3 = .ok 8 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem normalized_local4 (frame : CompilerFrameContext.ActualFrame)
    (sourceBody : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 4 = .ok 5 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [sourceBody,identity,callee]
  with_unfolding_all rfl

theorem compute_local (framesBefore : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (ty : TyId) (layout : LocalLayout)
    (normalized : CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame localId = .ok ty)
    (lookup : PreparedReflection.actual.compiler.runtime.lookup ty = .ok layout) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler localId
      (Storage.withCurrent framesBefore frame machine) =
    .ok layout (Storage.withCurrent framesBefore frame machine) := by
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [normalized]
  unfold_frame_query_lift
  simp only [pure, EStateM.pure, bind, EStateM.bind]
  rw [lookup]
  rfl

#print axioms normalized_local0
#print axioms normalized_local3
#print axioms normalized_local4
#print axioms compute_local
end DuplicatePrefix.PointerAddFacts
