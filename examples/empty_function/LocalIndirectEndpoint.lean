import empty_function.LocalIndirectInit
import empty_function.LocalIndirectReturn
import empty_function.LocalModel
import empty_function.WildcardEndpoint
namespace EmptyFunction.LocalIndirectEndpoint
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration EmptyFunction.WildcardInit
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
private theorem two_step_noErrors (s : Static) (depth : Nat) (start middle finish : State)
    (first : ExecutionMachine.step s.cfg s.limits () start = (middle,.ok true))
    (second : ExecutionMachine.step s.cfg s.limits () middle = (finish,.ok true))
    (outside : finish.stack.frames.size < depth) :
    ScopedSafety.NoErrors s.cfg s.limits (fun _ _ => True) depth start := by
  apply ScopedSafety.noErrors_of_invariant (fun state => state = start ∨ state = middle ∨ state = finish)
  · exact Or.inl rfl
  · intro before after choice phase inside permitted step
    cases choice
    rcases phase with rfl | rfl | rfl
    · rw [first] at step
      cases step
      exact Or.inr (Or.inl rfl)
    · rw [second] at step
      cases step
      exact Or.inr (Or.inr rfl)
    · omega
  · intro state phase inside choice permitted
    cases choice
    rcases phase with rfl | rfl | rfl
    · exact ⟨middle,true,first⟩
    · exact ⟨finish,true,second⟩
    · omega

private theorem initialized_active (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F)
    (thread : Concurrency.ThreadRecord) (active : p.before.machine.threads.activeThread? = some thread) :
    ∃ current, (LocalModel.initializedMachine s p tracker destination older bound frame previous).threads.activeThread? = some current := by
  have fields := MetadataBinding.fields s metadata capacity
  unfold LocalModel.initializedMachine FrameRelevance.pushedMachine
  rw [fields.freshLocalsIdentity]
  split
  · refine ⟨{thread with topUserRelevantFrame := some (older.push (LocalModel.caller s p tracker destination bound)).size},?_⟩
    change (p.before.machine.threads.threads.mapIdx (fun index old =>
      if index == p.before.machine.threads.activeThread.toNat then
        {old with topUserRelevantFrame := some (older.push (LocalModel.caller s p tracker destination bound)).size} else old))[p.before.machine.threads.activeThread.toNat]? = _
    rw [List.getElem?_mapIdx]
    change p.before.machine.threads.threads[p.before.machine.threads.activeThread.toNat]? = some thread at active
    rw [active]
    simp
  · exact ⟨thread,active⟩
private theorem initialized_control (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) :
    (LocalModel.initializedMachine s p tracker destination older bound frame previous).user.payload.payload.user.host.control =
      p.before.machine.user.payload.payload.user.host.control := by
  have fields := MetadataBinding.fields s metadata capacity
  unfold LocalModel.initializedMachine FrameRelevance.pushedMachine
  rw [fields.freshLocalsIdentity]
  split <;> rfl
private theorem initialized_fixed (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) :
    (LocalModel.initializedMachine s p tracker destination older bound frame previous).threads.fixedScheduling =
      p.before.machine.threads.fixedScheduling := by
  have fields := MetadataBinding.fields s metadata capacity
  unfold LocalModel.initializedMachine FrameRelevance.pushedMachine
  rw [fields.freshLocalsIdentity]
  split <;> rfl

def initializedMachine (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) :=
  UnitRetag.allocatedMachine (LocalModel.initializedMachine s p tracker destination older bound frame previous) tracker room

def finishedMachine (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (choice : Case p tracker room) (index : Nat) :=
  let frames := older.push (LocalModel.caller s p tracker destination bound)
  let base := (TerminatorStep.after (LocalUnit.current frames frame
    (initializedMachine s p tracker destination older bound frame previous room))).machine
  FrameExit.afterRelevanceAt frames frame (WildcardEndpoint.released choice base) index

theorem run_operations (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p)
    (destination : InputDraft.LocalDestination s p input.tracker)
    (whole : destination.offset = none) (place : MemPlace Provenance)
    (indirect : destination.oldOperand = .indirect place)
    (resident : ProtectionDispatch.Resident s p place.ptr) :
    ∃ (older : Array LocalUnit.F) (bound : destination.localId < destination.caller.locals.size)
      (choice : Case p input.tracker (ConcreteProtection.tag_room s p input resources))
      (installed finish : State) (frame previous : LocalUnit.F) (index : Nat),
      p.before.stack.frames = older.push destination.caller ∧
      WholeCall.install s p = .ok () installed ∧ installed.stack.frames.size = depth p ∧
      Executes s (depth p) installed finish ∧ Returned p finish ∧
      ScopedSafety.NoErrors s.cfg s.limits (fun _ _ => True) (depth p) installed ∧
      ScopedSafety.NoUB s.cfg s.limits (fun _ _ => True) (depth p) installed ∧
      finish = ReturnContinuation.resume older (LocalModel.caller s p input.tracker destination bound)
        (finishedMachine s p input.tracker destination older bound frame previous
          (ConcreteProtection.tag_room s p input resources) choice index) p.returnBlock := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  have positive : 0 < s.capacity := by have bound := resources.capacity; omega
  obtain ⟨remaining,capacity⟩ : ∃ n : Nat, s.capacity = n+2 :=
    ⟨s.capacity-2,by have bound := resources.capacity; omega⟩
  have validation : 0 < s.options.limits.validation := by have bound := resources.configuredValidation; omega
  obtain ⟨older,bound,original,⟨entry⟩⟩ := LocalIndirectInit.install_whole s metadata profile p runtime input resources destination whole place indirect resident
  let caller := LocalModel.caller s p input.tracker destination bound
  let frames := older.push caller
  let frame := {(BodyStep.withUnit entry.frame .uninit (some s.abi.ret.layout)) with location := .mir ⟨0,1⟩}
  have entrySame : BodyStep.withUnit entry.frame .uninit none = entry.frame := by
    change {entry.frame with locals := #[{value := .live (.immediate .uninit),layout := none}]} = entry.frame
    rw [←entry.locals]
  have first := BodyAssignment.step s metadata profile remaining capacity validation frames
    entry.frame entry.machine entry.identity entry.body entry.function entry.location entry.noClocks entry.ghost entry.shallow
  rw [entrySame] at first
  let installed := LocalUnit.current frames entry.frame entry.machine
  let middle := LocalUnit.current frames frame entry.machine
  have depthEq : installed.stack.frames.size = depth p := by simp [installed,LocalUnit.current,depth,frames,caller,LocalModel.caller,LocalInit.cachedState,original]
  have body : frame.body = s.loaded.body := entry.body
  have location : frame.location = .mir ⟨0,1⟩ := rfl
  have locals : frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}] := rfl
  have noClocks : frame.extra.dataRace = none := entry.noClocks
  have frameTracked : frame.extra.borrowTracker = some (borrow entry.choice) := entry.tracked
  have returnPlace : frame.returnPlace = p.destination := entry.returnPlace
  have varargs : frame.vaList = #[] := entry.varargs
  have continuation : frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind) := entry.continuation
  let room := ConcreteProtection.tag_room s p input resources
  let canonical := initializedMachine s p input.tracker destination older bound frame entry.previous room
  have machineEq : entry.machine = entered entry.choice
      (FrameRelevance.pushedMachine frames frame entry.previous
        (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1) := entry.machineEq
  have controlEq : entry.machine.user.payload.payload.user.host.control =
      p.before.machine.user.payload.payload.user.host.control := by
    rw [machineEq]
    cases entry.choice <;> change canonical.user.payload.payload.user.host.control = _
    all_goals change (LocalModel.initializedMachine s p input.tracker destination older bound frame entry.previous).user.payload.payload.user.host.control = _
    all_goals exact initialized_control s metadata positive p input.tracker destination older bound frame entry.previous
  have fixed : entry.machine.threads.fixedScheduling = true := by
    rw [machineEq]
    cases entry.choice <;> change canonical.threads.fixedScheduling = true
    all_goals change (LocalModel.initializedMachine s p input.tracker destination older bound frame entry.previous).threads.fixedScheduling = true
    all_goals rw [initialized_fixed s metadata positive]; exact runtime.fixedScheduling
  obtain ⟨thread,activeCanonical⟩ := initialized_active s metadata positive p input.tracker destination older bound frame entry.previous
    input.thread input.active
  have gc : entry.machine.user.payload.payload.user.host.control.gcInterval = 0 := by rw [controlEq];exact runtime.gc
  have unchecked : entry.machine.user.payload.payload.user.host.control.checkedArithmetic = false := by rw [controlEq];exact runtime.unchecked
  let post := (TerminatorStep.after middle).machine
  let base := (TerminatorStep.after (LocalUnit.current frames frame canonical)).machine
  have baseTracked : base.borrowTracker = some (UnitRetag.allocatedTracker input.tracker room) := rfl
  have baseActive : base.threads.activeThread? = some thread := activeCanonical
  have hook := TerminatorStep.canonical s metadata positive middle fixed gc unchecked
  have hookEq : (ExecutionMachine.stepHooks s.cfg s.limits).beforeTerminator () middle =
      (LocalUnit.current frames frame post,.ok ()) := hook
  let ended := WildcardEndpoint.released entry.choice base
  let finalMachine := FrameExit.afterRelevanceAt (older.push caller) frame ended
    (thread.topUserRelevantFrame.getD (older.push caller).size)
  let finish := ReturnContinuation.resume older caller finalMachine p.returnBlock
  have popped : (ReturnStep.control s).popFrame () (LocalUnit.current (older.push caller) frame post) =
      ((⟨⟨older.push caller⟩,finalMachine⟩ : State),.ok frame) := by
    cases choiceEq : entry.choice with
    | miss =>
      have tracked : frame.extra.borrowTracker = some {} := by simpa [choiceEq,borrow] using frameTracked
      have postEq : post = base := by dsimp only [post,base,middle];rw [machineEq,choiceEq];rfl
      have popping := ReturnStep.pop s (older.push caller) frame base
        (UnitRetag.allocatedTracker input.tracker room) baseTracked tracked thread baseActive
      simpa only [finalMachine,ended,WildcardEndpoint.released,choiceEq,postEq] using popping
    | nondata id registry =>
      let emptyBase := {frame with extra := {frame.extra with borrowTracker := some {}}}
      have registered : UnitRetag.registeredFrame emptyBase {} id input.tracker.global.nextPointerTag = frame := by
        change {frame with extra := {frame.extra with borrowTracker := some {protectedTags := #[(id,input.tracker.global.nextPointerTag)]}}} = frame
        have tracked : frame.extra.borrowTracker = some {protectedTags := #[(id,input.tracker.global.nextPointerTag)]} := by simpa only [choiceEq,borrow] using frameTracked
        rw [←tracked]
      have postEq : post = UnitRetag.registeredMachine base (UnitRetag.allocatedTracker input.tracker room) input.tracker.global.nextPointerTag := by
        dsimp only [post,base,middle];rw [machineEq,choiceEq];rfl
      have memory : base.memory = p.before.machine.memory := by
        have fields := MetadataBinding.fields s metadata positive
        unfold base canonical TerminatorStep.after initializedMachine LocalModel.initializedMachine UnitRetag.allocatedMachine FrameRelevance.pushedMachine
        rw [fields.freshLocalsIdentity]
        split <;> rfl
      have popping := ReturnNondata.pop s metadata positive (older.push caller) emptyBase base input.tracker room
        baseTracked input.world.globals p id registry memory thread baseActive
      rw [registered,←postEq] at popping
      simpa only [finalMachine,ended,WildcardEndpoint.released,choiceEq] using popping
    | live id old live tree release rights =>
      let emptyBase := {frame with extra := {frame.extra with borrowTracker := some {}}}
      have registered : UnitRetag.registeredFrame emptyBase {} id input.tracker.global.nextPointerTag = frame := by
        change {frame with extra := {frame.extra with borrowTracker := some {protectedTags := #[(id,input.tracker.global.nextPointerTag)]}}} = frame
        have tracked : frame.extra.borrowTracker = some {protectedTags := #[(id,input.tracker.global.nextPointerTag)]} := by simpa only [choiceEq,borrow] using frameTracked
        rw [←tracked]
      have postEq : post = {UnitRetag.registeredMachine base (UnitRetag.allocatedTracker input.tracker room)
          input.tracker.global.nextPointerTag with memory := UnitRetag.replaceTree base.memory id old tree} := by
        dsimp only [post,base,middle];rw [machineEq,choiceEq];rfl
      have popping := ReturnSingleton.pop s metadata positive (older.push caller) emptyBase base input.tracker room
        baseTracked input.world.globals id old tree release thread baseActive
      rw [registered,←postEq] at popping
      simpa only [finalMachine,ended,WildcardEndpoint.released,choiceEq] using popping
  have ghostCanonical : canonical.user.payload.ghost = false := by
    have h := entry.ghost
    rw [machineEq] at h
    cases choiceEq : entry.choice <;> rw [choiceEq] at h <;> exact h
  have shallowCanonical : canonical.user.payload.validation = .Shallow := by
    have h := entry.shallow
    rw [machineEq] at h
    cases choiceEq : entry.choice <;> rw [choiceEq] at h <;> exact h
  have ghostPost : finalMachine.user.payload.ghost = false := by
    unfold finalMachine ended FrameExit.afterRelevanceAt FrameExit.afterRelevance
    split <;> cases entry.choice <;> exact ghostCanonical
  have shallowPost : finalMachine.user.payload.validation = .Shallow := by
    unfold finalMachine ended FrameExit.afterRelevanceAt FrameExit.afterRelevance
    split <;> cases entry.choice <;> exact shallowCanonical
  obtain ⟨unwind,normalCont⟩ : ∃ unwind,
      frame.returnContinuation = .goto (some p.returnBlock) unwind := by
    rw [continuation]
    unfold CanonicalInit.normalizedContinuation
    split <;> exact ⟨_,rfl⟩
  have cachedAt := LocalImmediate.cached_at destination.caller destination.localId destination.slot s.abi.ret.layout bound
  have oldLive : destination.slot.value = .live (.indirect place) := by rw [destination.live,indirect]
  have copyEq := LocalIndirectReturn.copy s metadata profile remaining capacity validation older caller finalMachine
    destination.localId {destination.slot with layout := some s.abi.ret.layout} place cachedAt oldLive rfl
    (destination.oldRepresentation place indirect).1 (destination.oldRepresentation place indirect).2
    (show caller.extra.dataRace = none from by
      have same : destination.caller = input.caller := Option.some.inj (destination.current.symm.trans input.current)
      change destination.caller.extra.dataRace = none
      rw [same];exact input.callerNoClocks) ghostPost shallowPost
  have returning : frame.returnPlace = .frameLocal older.size destination.localId none s.abi.ret.layout caller.localsIdentity := by
    rw [returnPlace,destination.encoding,whole,original]
    simp [caller,LocalModel.caller,LocalImmediate.cached]
  rw [←returning] at copyEq
  have returned := ReturnCore.core s metadata profile remaining capacity validation older caller frame post finalMachine
    body location locals noClocks popped copyEq p.returnBlock unwind normalCont varargs ghostPost shallowPost
  have returnEq : (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame () false
      (LocalUnit.current frames frame post) = (finish,.ok ()) := by
    simpa only [original] using returned
  have second := ReturnStep.compose s metadata frames frame entry.machine post finish body location hookEq returnEq
  have outside : finish.stack.frames.size < depth p := by simp [finish,ReturnContinuation.resume,depth,original]
  have inside : depth p ≤ middle.stack.frames.size := by simp [depth,middle,LocalUnit.current,frames,original]
  have trace : Executes s (depth p) installed finish :=
    Executes.next (by omega) first (Executes.next inside second (Executes.refl _))
  have returnedToCaller : Returned p finish := by
    refine ⟨?_,?_,destination.caller,{caller with location := .mir ⟨p.returnBlock,0⟩},destination.current,?_,rfl,rfl,rfl,rfl,rfl⟩
    · simp [finish,ReturnContinuation.resume,original]
    · simp [finish,ReturnContinuation.resume,original]
    · simp [finish,ReturnContinuation.resume,Stack.currentFrame?]
  have safe := two_step_noErrors s (depth p) installed middle finish first second outside
  refine ⟨older,bound,entry.choice,installed,finish,frame,entry.previous,
    thread.topUserRelevantFrame.getD (older.push caller).size,original,entry.installed,depthEq,trace,
    returnedToCaller,safe,ScopedSafety.noUB_of_noErrors safe,?_⟩
  rfl
end EmptyFunction.LocalIndirectEndpoint
