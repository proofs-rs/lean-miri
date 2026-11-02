import empty_function.ProjectedImmediatePreflight
import empty_function.LocalCachedPush
namespace EmptyFunction.ProjectedImmediateInit
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
 theorem install (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    {choiceCondition : Prop} (resources : ResourceMargins s p choiceCondition) (destination : InputDraft.LocalDestination s p input.tracker)
    (offset : Size) (projected : destination.offset = some offset) (value : Immediate Provenance)
    (immediate : destination.oldOperand = .immediate value) :
    ∃ (older : Array LocalUnit.F) (bound : destination.localId < destination.caller.locals.size)
      (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser),
      p.before.stack.frames = older.push destination.caller ∧
      WholeCall.install s p = .ok () (LocalUnit.current (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames frame machine) ∧
      frame.body = s.loaded.body ∧ frame.bodyIdentity = s.loaded.identity ∧
      frame.functionInstance = s.functionInstance ∧ frame.location = .mir ⟨0,0⟩ ∧
      frame.locals = #[{value := .live (.immediate .uninit),layout := none}] ∧
      frame.extra.borrowTracker = some {} ∧ frame.extra.dataRace = none ∧ frame.returnPlace = p.destination ∧
      frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind) ∧
      frame.vaList = #[] ∧ machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
      (∃ previous, machine = FrameRelevance.pushedMachine (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames
        frame previous (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1) ∧
      machine.borrowTracker = p.before.machine.borrowTracker := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  have capacity : 0 < s.capacity := by have bound := resources.capacity; omega
  have fields := MetadataBinding.fields s metadata capacity
  obtain ⟨older,original⟩ := Array.back?_eq_some_iff.mp destination.current
  have bound : destination.localId < destination.caller.locals.size := Array.getElem?_eq_some_iff.mp destination.slotAt |>.1
  have sameCaller : destination.caller = input.caller := Option.some.inj (destination.current.symm.trans input.current)
  have noClocks : destination.caller.extra.dataRace = none := by rw [sameCaller]; exact input.callerNoClocks
  have preflight := ProjectedImmediatePreflight.canonical s metadata profile capacity p input.tracker destination offset projected value immediate
    noClocks older original bound
  let continuation : ReturnContinuation := .goto (some p.returnBlock) p.unwind
  have initial := Call.zero_entry_immediate (ExecutionMachine.callHooks s.cfg s.limits) () s.functionInstance
    s.loaded s.abi p.destination continuation p.before (LocalCachedPush.cachedState s p input.tracker destination older bound)
    .uninit s.abi.ret.layout (MetadataBinding.caller_location s metadata capacity)
    (MetadataBinding.instance_abi s metadata capacity) (MetadataBinding.target_features s metadata capacity)
    preflight (MetadataBinding.not_closure s metadata capacity) metadata.notVariadic
    (show (ExecutionMachine.callHooks s.cfg s.limits).sameConvention s.abi s.abi = true from beq_self_eq_true _)
    metadata.noArguments rfl (by rw [metadata.body]; exact Program.no_arguments)
  rw [LocalInit.core_reduction s metadata capacity] at initial
  obtain ⟨frame,machine,push,⟨previous,machineEq⟩,tracked,frameNoClocks,body,identity,function,location,
    returning,returnPlace,locals,varargs,callerArg,machineTracker,machineRace⟩ :=
      LocalCachedPush.push_cached s metadata profile p runtime input capacity destination older original bound
        (CanonicalInit.normalizedContinuation s continuation)
  have cleared : {frame with trackCallerArg := none} = frame := by rw [←callerArg]
  have localQuery := CanonicalInit.local_span s metadata capacity
    (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames frame machine identity function body
  have done := CanonicalInit.push_done s metadata capacity
    (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames frame machine body locals frameNoClocks
  have result : LocalInit.rawCore s p.destination continuation (LocalCachedPush.cachedState s p input.tracker destination older bound) =
      .ok () (LocalUnit.current (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames {frame with
        locals := #[{value := .live (.immediate .uninit),layout := none}],location := .mir .start} machine) := by
    unfold LocalInit.rawCore
    simp only [bind,EStateM.bind]
    rw [push]
    dsimp only
    have currentEq := CanonicalInit.get_current (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames frame machine
    simp only [LocalUnit.current] at currentEq
    rw [currentEq]
    simp only [location,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
    have setEq := CanonicalInit.set_current (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames
      frame {frame with trackCallerArg := none} machine
    simp only [LocalUnit.current,location] at setEq
    rw [setEq]
    simp only [←location,cleared]
    simp only [LocalUnit.current] at localQuery done
    rw [localQuery]
    dsimp only
    have spanEq := CanonicalInit.span_current metadata.localSpan
      (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames frame machine
    simp only [LocalUnit.current] at spanEq
    rw [spanEq]
    dsimp only
    have restoreEq := CanonicalInit.span_current metadata.preamble
      (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames
      {frame with location := .unwinding metadata.localSpan} machine
    simp only [LocalUnit.current] at restoreEq
    rw [restoreEq]
    simp only [←location]
    exact done
  let output : LocalUnit.F := {frame with locals := #[{value := .live (.immediate .uninit),layout := none}],location := .mir .start}
  have ghost : machine.user.payload.ghost = false := by
    simp [machineEq,FrameRelevance.pushedMachine,fields.freshLocalsIdentity,LocalCachedPush.cachedState,LocalUnit.current]
    split <;> change p.before.machine.user.payload.ghost = false
    all_goals exact runtime.ghost
  have shallow : machine.user.payload.validation = .Shallow := by
    simp [machineEq,FrameRelevance.pushedMachine,fields.freshLocalsIdentity,LocalCachedPush.cachedState,LocalUnit.current]
    split <;> change p.before.machine.user.payload.validation = .Shallow
    all_goals exact runtime.shallow
  have shape : machine = FrameRelevance.pushedMachine (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames
      output previous (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1 := by rw [machineEq]; rfl
  refine ⟨older,bound,output,machine,original,initial.trans result,body,identity,function,rfl,rfl,tracked,
    frameNoClocks,returnPlace,returning,varargs,ghost,shallow,⟨previous,shape⟩,machineTracker⟩

end EmptyFunction.ProjectedImmediateInit
