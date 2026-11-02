import empty_function.LocalIndirectFinish
import empty_function.ProtectionDispatch
import empty_function.LocalInit
namespace EmptyFunction.LocalIndirectInit
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration EmptyFunction.WildcardInit
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
structure Entry (s : Static) (p : Packet) (frames : Array LocalUnit.F) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) where
  choice : Case p tracker room
  frame : LocalUnit.F
  previous : LocalUnit.F
  machine : MachineHooks.MachineState MiriMemoryKind RootUser
  installed : WholeCall.install s p = .ok () (LocalUnit.current frames frame machine)
  body : frame.body = s.loaded.body
  identity : frame.bodyIdentity = s.loaded.identity
  function : frame.functionInstance = s.functionInstance
  location : frame.location = .mir ⟨0,0⟩
  locals : frame.locals = #[{value := .live (.immediate .uninit),layout := none}]
  tracked : frame.extra.borrowTracker = some (borrow choice)
  noClocks : frame.extra.dataRace = none
  returnPlace : frame.returnPlace = p.destination
  continuation : frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind)
  varargs : frame.vaList = #[]
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  machineEq : machine = entered choice (FrameRelevance.pushedMachine frames frame previous
    (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1)

theorem install_whole (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p)
    (destination : InputDraft.LocalDestination s p input.tracker)
    (whole : destination.offset = none) (place : MemPlace Provenance)
    (indirect : destination.oldOperand = .indirect place)
    (resident : ProtectionDispatch.Resident s p place.ptr) :
    ∃ (older : Array LocalUnit.F) (bound : destination.localId < destination.caller.locals.size),
      p.before.stack.frames = older.push destination.caller ∧
      Nonempty (Entry s p (LocalInit.cachedState s p input.tracker destination older bound).stack.frames
        input.tracker (ConcreteProtection.tag_room s p input resources)) := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  have capacity : 0 < s.capacity := by have bound := resources.capacity; omega
  have fields := MetadataBinding.fields s metadata capacity
  obtain ⟨older,original⟩ := Array.back?_eq_some_iff.mp destination.current
  have bound : destination.localId < destination.caller.locals.size := Array.getElem?_eq_some_iff.mp destination.slotAt |>.1
  have sameCaller : destination.caller = input.caller := Option.some.inj (destination.current.symm.trans input.current)
  have callerNoClocks : destination.caller.extra.dataRace = none := by rw [sameCaller];exact input.callerNoClocks
  have preflight := LocalIndirectPreflight.operand s metadata profile capacity p input.tracker destination whole place indirect
    callerNoClocks older original bound
  let room := ConcreteProtection.tag_room s p input resources
  let cached := LocalInit.cachedState s p input.tracker destination older bound
  let frames := cached.stack.frames
  obtain ⟨frame,machine,push,⟨previous,machineEq⟩,tracked,noClocks,body,identity,function,location,
    returning,returnPlace,locals,varargs,callerArg,machineTracker,machineRace⟩ :=
      LocalInit.push_cached s metadata profile p runtime input capacity destination older original bound
        (CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind))
  have enabled : machine.borrowTracker = some input.tracker := machineTracker.trans input.world.enabled
  have memoryEq : machine.memory = p.before.machine.memory := by
    rw [machineEq]
    unfold FrameRelevance.pushedMachine
    rw [fields.freshLocalsIdentity]
    split <;> rfl
  have addressesEq : machine.user.addresses = p.before.machine.user.addresses := by
    rw [machineEq]
    unfold FrameRelevance.pushedMachine
    rw [fields.freshLocalsIdentity]
    split <;> rfl
  let facts : ProtectionPlace.Input s p.before input.tracker :=
    ⟨⟨place,s.abi.ret.layout⟩,rfl,(destination.oldRepresentation place indirect).1,
      (destination.oldRepresentation place indirect).2,destination.oldPointer place indirect⟩
  obtain ⟨choice,protection⟩ := ProtectionDispatch.protect s metadata profile capacity p input resources facts resident frames
    {frame with location := .unwinding metadata.localSpan} machine enabled tracked memoryEq addressesEq
  let output : LocalUnit.F := {frame with locals := #[{value := .live (.immediate .uninit),layout := none}], location := .mir .start, extra := {frame.extra with borrowTracker := some (borrow choice)}}
  have installed := LocalIndirectFinish.finish s metadata capacity p facts.place cached frames preflight frame machine
    (entered choice machine) (borrow choice) push body identity function location locals noClocks callerArg protection
  have ghost : (entered choice machine).user.payload.ghost = false := by
    cases choice <;> simp only [entered,NondataProtection.protectedMachine,ConcreteProtection.protectedMachine,
      UnitRetag.registeredMachine,UnitRetag.allocatedMachine]
    all_goals rw [machineEq]
    all_goals unfold FrameRelevance.pushedMachine
    all_goals rw [fields.freshLocalsIdentity]
    all_goals split <;> exact runtime.ghost
  have shallow : (entered choice machine).user.payload.validation = .Shallow := by
    cases choice <;> simp only [entered,NondataProtection.protectedMachine,ConcreteProtection.protectedMachine,
      UnitRetag.registeredMachine,UnitRetag.allocatedMachine]
    all_goals rw [machineEq]
    all_goals unfold FrameRelevance.pushedMachine
    all_goals rw [fields.freshLocalsIdentity]
    all_goals split <;> exact runtime.shallow
  refine ⟨older,bound,original,⟨⟨choice,output,previous,entered choice machine,installed,body,identity,function,rfl,rfl,rfl,
    noClocks,returnPlace,returning,varargs,ghost,shallow,?_⟩⟩⟩
  rw [machineEq]
  rfl
end EmptyFunction.LocalIndirectInit
