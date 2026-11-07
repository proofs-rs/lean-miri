import empty_function.LocalPreparation
import empty_function.LocalIndirectCore
namespace EmptyFunction.LocalIndirectPrefix
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- Source call suffix for the original local return place. The original
packet is retained; only its actual preflight state and pushed frame appear. -/
theorem at_protection (s : Static) (metadata : Metadata s) (p : Packet)
    (place : MPlaceTy Provenance) (cached : State) (frames : Array LocalUnit.F)
    (preflight : (ExecutionMachine.callHooks s.cfg s.limits).placeToOp () p.destination p.before =
      .ok ⟨.indirect place.mplace,place.layout⟩ cached)
    (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind Configuration.RootUser)
    (push : (ExecutionMachine.callHooks s.cfg s.limits).pushRaw () s.functionInstance s.loaded
      p.destination (CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind)) cached =
      .ok () (LocalUnit.current frames frame machine))
    (body : Meaning.FrameMatches frame s.loaded) (identity : frame.bodyIdentity = s.loaded.identity)
    (function : frame.functionInstance = s.functionInstance)
    (location : frame.location = .unwinding metadata.preamble) (callerArg : frame.trackCallerArg = none) :
    install s p = InitializationPrefix.protectedTail s place metadata.preamble
      (LocalUnit.current frames {frame with location := .unwinding metadata.localSpan} machine) := by
  unfold install
  rw [LocalIndirectCore.entry_core s metadata (InitializationPrefix.capacity_positive s) p.destination place
    (.goto (some p.returnBlock) p.unwind) p.before cached preflight]
  have cleared : {frame with trackCallerArg := none} = frame := by rw [←callerArg]
  have localQuery := CanonicalInit.local_span s metadata (InitializationPrefix.capacity_positive s)
    frames frame machine identity function body
  unfold LocalIndirectCore.rawCore
  simp only [bind,EStateM.bind]
  rw [push]
  change (do
    let current ← MachineHooks.currentFrame
    let preamble ← match current.location with
      | .unwinding span => pure span
      | .mir _ => throw (StepError.invalidProgram "raw frame does not have preamble location")
    MachineHooks.setCurrentFrame {current with trackCallerArg := none}
    CanonicalInit.spanAt (← (ExecutionMachine.callHooks s.cfg s.limits).localSpan s.loaded.identity 0)
    (ExecutionMachine.callHooks s.cfg s.limits).protectArgument () place
    CanonicalInit.spanAt preamble
    (ExecutionMachine.callHooks s.cfg s.limits).pushDone ())
      (LocalUnit.current frames frame machine) = _
  simp only [bind,EStateM.bind]
  rw [CanonicalInit.get_current]
  simp only [location,EStateM.bind,pure,Pure.pure,EStateM.pure]
  rw [CanonicalInit.set_current]
  simp only [←location,cleared]
  rw [localQuery]
  dsimp only
  rw [CanonicalInit.span_current]
  rfl

/-- The effective memory place of an already-indirect caller local, including
inclusive end projections. This computes a raw pointer, not a successful action. -/
def selectedPlace (place : MemPlace Provenance) (offset : Option Size) : MemPlace Provenance :=
  match offset with
  | none => place
  | some amount => ProjectedIndirectPreflight.shifted place amount

theorem prepare (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker)
    (place : MemPlace Provenance) (indirect : destination.oldOperand = .indirect place)
    (older : Array LocalUnit.F) (original : p.before.stack.frames = older.push destination.caller)
    (bound : destination.localId < destination.caller.locals.size) :
    (ExecutionMachine.callHooks s.cfg s.limits).placeToOp () p.destination p.before =
      .ok ⟨.indirect (selectedPlace place destination.offset),s.abi.ret.layout⟩
        (LocalCachedPush.cachedState s p input.tracker destination older bound) := by
  have capacity := InitializationPrefix.capacity_positive s
  cases offset : destination.offset with
  | none =>
    have layout : destination.baseLayout = s.abi.ret.layout := by
      cases destination
      cases offset
      assumption
    have sameCaller : destination.caller = input.caller :=
      Option.some.inj (destination.current.symm.trans input.current)
    have noClocks : destination.caller.extra.dataRace = none := by
      rw [sameCaller]; exact input.callerNoClocks
    simpa only [selectedPlace,offset,LocalCachedPush.cachedState,layout] using
      LocalIndirectPreflight.operand s metadata profile capacity p input.tracker destination offset place indirect
        noClocks older original bound
  | some amount =>
    simpa only [selectedPlace,offset] using
      ProjectedIndirectPreflight.operand s metadata profile capacity p input.tracker destination amount offset
        place indirect older original bound

/-- Effective-pointer classification stays anchored to the original local
packet, even when a one-past wildcard denotes a neighboring allocation. -/
theorem effective (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (place : MemPlace Provenance)
    (indirect : destination.oldOperand = .indirect place) :
    InputDraft.effectivePointer p = some (selectedPlace place destination.offset).ptr := by
  cases offset : destination.offset <;>
    simp [InputDraft.effectivePointer,destination.encoding,destination.current,destination.slotAt,
      destination.live,indirect,selectedPlace,ProjectedIndirectPreflight.shifted,offset,
      bind,Bind.bind,Option.bind,pure,Pure.pure]

/-- Both whole and projected already-indirect locals reach exactly the same
protection/tail interface as memory destinations, retaining the original
frameLocal packet and the actual cache-only caller update. -/
theorem local_prefix (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker)
    (place : MemPlace Provenance) (indirect : destination.oldOperand = .indirect place) :
    ∃ (older : Array LocalUnit.F) (bound : destination.localId < destination.caller.locals.size)
      (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind Configuration.RootUser),
      p.before.stack.frames = older.push destination.caller ∧
      install s p = InitializationPrefix.protectedTail s
        ⟨selectedPlace place destination.offset,s.abi.ret.layout⟩ metadata.preamble
        (LocalUnit.current (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames
          {frame with location := .unwinding metadata.localSpan} machine) ∧
      Meaning.FrameMatches frame s.loaded ∧ frame.bodyIdentity = s.loaded.identity ∧
      frame.functionInstance = s.functionInstance ∧ frame.location = .unwinding metadata.preamble ∧
      frame.locals = #[{value := .dead,layout := none}] ∧
      frame.extra.borrowTracker = some {} ∧ frame.extra.dataRace = none ∧
      frame.returnPlace = p.destination ∧
      frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind) ∧
      frame.vaList = #[] ∧ frame.trackCallerArg = none ∧
      machine.borrowTracker = some input.tracker ∧ machine.dataRace = none ∧
      machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
      ∃ previous, machine = FrameRelevance.pushedMachine
        (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames frame previous
        (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1 := by
  have capacity := InitializationPrefix.capacity_positive s
  obtain ⟨older,original⟩ := Array.back?_eq_some_iff.mp destination.current
  have bound : destination.localId < destination.caller.locals.size :=
    (Array.getElem?_eq_some_iff.mp destination.slotAt).1
  have preflight := prepare s metadata profile p input destination place indirect older original bound
  obtain ⟨frame,machine,push,previous,tracked,noClocks,body,identity,function,location,
      returning,returnPlace,locals,varargs,callerArg,machineTracker,machineRace⟩ :=
    LocalCachedPush.push_cached s metadata profile p runtime input capacity destination older original bound
      (CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind))
  have prefixEq := at_protection s metadata p ⟨selectedPlace place destination.offset,s.abi.ret.layout⟩
    (LocalCachedPush.cachedState s p input.tracker destination older bound)
    (LocalCachedPush.cachedState s p input.tracker destination older bound).stack.frames preflight
    frame machine push body identity function location callerArg
  refine ⟨older,bound,frame,machine,original,prefixEq,body,identity,function,location,locals,tracked,
    noClocks,returnPlace,returning,varargs,callerArg,?_,machineRace,?_,?_,previous⟩
  · change machine.borrowTracker = p.before.machine.borrowTracker at machineTracker
    rw [machineTracker,input.world.enabled]
  · obtain ⟨previous,machineEq⟩ := previous
    simp [machineEq,FrameRelevance.pushedMachine,
      (MetadataBinding.fields s metadata capacity).freshLocalsIdentity]
    split <;> change p.before.machine.user.payload.ghost = false
    all_goals exact runtime.ghost
  · obtain ⟨previous,machineEq⟩ := previous
    simp [machineEq,FrameRelevance.pushedMachine,
      (MetadataBinding.fields s metadata capacity).freshLocalsIdentity]
    split <;> change p.before.machine.user.payload.validation = .Shallow
    all_goals exact runtime.shallow

end EmptyFunction.LocalIndirectPrefix
