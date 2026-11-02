import duplicate_prefix.RootDivisor
import duplicate_prefix.PointerAddFacts
namespace DuplicatePrefix.RootGuardFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem normalized_local8 (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 8 = .ok 0 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body,identity,callee]
  with_unfolding_all rfl

theorem normalized_local10 (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 10 = .ok 5 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body,identity,callee]
  with_unfolding_all rfl

#print axioms normalized_local8
#print axioms normalized_local10
end DuplicatePrefix.RootGuardFacts
