import duplicate_prefix.AsMutPtrFacts
import duplicate_prefix.Storage
import duplicate_prefix.CanonicalConfigFacts
namespace DuplicatePrefix.AsMutPtrLayouts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem normalized (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (id : Miri.MIR.LocalId) (which : id = 0 ∨ id = 2 ∨ id = 3 ∨ id = 4) :
    CompilerFrameContext.localType PreparedReflection.actual.compiler frame id =
      .ok (if id = 0 ∨ id = 2 then 8 else 99) := by
  unfold CompilerFrameContext.localType CompilerFrameContext.bodyOfFrame
  rw [body,identity,callee]
  rcases which with rfl | rfl | rfl | rfl <;> with_unfolding_all rfl

theorem compute
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (id : Miri.MIR.LocalId) (which : id = 0 ∨ id = 2 ∨ id = 3 ∨ id = 4) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler id (Storage.withCurrent frames frame machine) =
      .ok (if id = 0 ∨ id = 2 then CopyCompilerFacts.destPointerLayout else AsMutPtrFacts.rawLayout)
        (Storage.withCurrent frames frame machine) := by
  have norm := normalized frame body identity callee id which
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame,Storage.withCurrent,Stack.currentFrame?,Array.back?_push,
    bind,EStateM.bind,get,getThe,MonadStateOf.get,EStateM.get,pure,EStateM.pure]
  rw [norm]
  rcases which with rfl | rfl | rfl | rfl
  all_goals simp only [show (0 : Miri.MIR.LocalId) ≠ 2 by decide,show (2 : Miri.MIR.LocalId) ≠ 0 by decide,
    show (3 : Miri.MIR.LocalId) ≠ 0 by decide,show (3 : Miri.MIR.LocalId) ≠ 2 by decide,
    show (4 : Miri.MIR.LocalId) ≠ 0 by decide,show (4 : Miri.MIR.LocalId) ≠ 2 by decide,
    or_self,or_true,true_or,ite_true,ite_false]
  all_goals unfold_internal ".CompilerFrameContext.lift"
  all_goals simp only [Except.mapError, Except.bind,pure,Pure.pure,EStateM.pure]
  all_goals first
    | (rw [show PreparedReflection.actual.compiler.runtime.lookup 8 = .ok CopyCompilerFacts.destPointerLayout from CopyCompilerFacts.dest_pointer_layout_eq]; rfl)
    | (rw [show PreparedReflection.actual.compiler.runtime.lookup 99 = .ok AsMutPtrFacts.rawLayout from AsMutPtrFacts.raw_layout_eq]; rfl)

end DuplicatePrefix.AsMutPtrLayouts
