import empty_function.WildcardInit
import empty_function.ConcretePost
import empty_function.ReturnNondata
namespace EmptyFunction.WildcardEndpoint
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration EmptyFunction.WildcardInit
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
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
    (p : Packet) (frame previous : LocalUnit.F) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (thread : Concurrency.ThreadRecord) (active : p.before.machine.threads.activeThread? = some thread) :
    ∃ current, (CanonicalInit.initializedMachine s p frame previous tracker room).threads.activeThread? = some current := by
  have fields := MetadataBinding.fields s metadata capacity
  unfold CanonicalInit.initializedMachine UnitRetag.allocatedMachine FrameRelevance.pushedMachine
  rw [fields.freshLocalsIdentity]
  split
  · refine ⟨{thread with topUserRelevantFrame := some p.before.stack.frames.size},?_⟩
    change (p.before.machine.threads.threads.mapIdx (fun index old =>
      if index == p.before.machine.threads.activeThread.toNat then
        {old with topUserRelevantFrame := some p.before.stack.frames.size} else old))[p.before.machine.threads.activeThread.toNat]? = _
    rw [List.getElem?_mapIdx]
    change p.before.machine.threads.threads[p.before.machine.threads.activeThread.toNat]? = some thread at active
    rw [active]
    simp
  · exact ⟨thread,active⟩
private theorem initialized_control (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (frame previous : LocalUnit.F) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) :
    (CanonicalInit.initializedMachine s p frame previous tracker room).user.payload.payload.user.host.control =
      p.before.machine.user.payload.payload.user.host.control := by
  have fields := MetadataBinding.fields s metadata capacity
  unfold CanonicalInit.initializedMachine UnitRetag.allocatedMachine FrameRelevance.pushedMachine
  rw [fields.freshLocalsIdentity]
  split <;> rfl
private theorem initialized_fixed (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (frame previous : LocalUnit.F) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) :
    (CanonicalInit.initializedMachine s p frame previous tracker room).threads.fixedScheduling =
      p.before.machine.threads.fixedScheduling := by
  have fields := MetadataBinding.fields s metadata capacity
  unfold CanonicalInit.initializedMachine UnitRetag.allocatedMachine FrameRelevance.pushedMachine
  rw [fields.freshLocalsIdentity]
  split <;> rfl


def released {p : Packet} {tracker : MachineHooks.BorrowState}
    {room : tracker.global.nextPointerTag.value < 18446744073709551615}
    (choice : Case p tracker room) (machine : MachineHooks.MachineState MiriMemoryKind RootUser) :=
  match choice with
  | .miss => machine
  | .nondata _ _ => machine
  | .live id entry _ tree _ _ => {machine with memory := UnitRetag.replaceTree machine.memory id entry tree}

theorem result (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p)
    (destination : InputDraft.MemoryDestination s p input.tracker)
    (wild : destination.place.mplace.ptr.provenance = some .wildcard)
    (resident : Resident s p destination.place.mplace.ptr) :
    WholeCall.Result s (Preservation.Preserves s) p := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  have positive : 0 < s.capacity := by have bound := resources.capacity; omega
  obtain ⟨remaining,capacity⟩ : ∃ n : Nat, s.capacity = n+2 :=
    ⟨s.capacity-2,by have bound := resources.capacity; omega⟩
  have validation : 0 < s.options.limits.validation := by have bound := resources.configuredValidation; omega
  obtain ⟨entry⟩ := WildcardInit.install s metadata profile p runtime input resources destination wild resident
  let frame := {(BodyStep.withUnit entry.frame .uninit (some s.abi.ret.layout)) with location := .mir ⟨0,1⟩}
  have entrySame : BodyStep.withUnit entry.frame .uninit none = entry.frame := by
    change {entry.frame with locals := #[{value := .live (.immediate .uninit),layout := none}]} = entry.frame
    rw [←entry.locals]
  have first := BodyAssignment.step s metadata profile remaining capacity validation p.before.stack.frames
    entry.frame entry.machine entry.identity entry.body entry.function entry.location entry.noClocks entry.ghost entry.shallow
  rw [entrySame] at first
  let installed := LocalUnit.current p.before.stack.frames entry.frame entry.machine
  let middle := LocalUnit.current p.before.stack.frames frame entry.machine
  have depthEq : installed.stack.frames.size = depth p := by simp [installed,LocalUnit.current,depth]
  have body : frame.body = s.loaded.body := entry.body
  have location : frame.location = .mir ⟨0,1⟩ := rfl
  have locals : frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}] := rfl
  have noClocks : frame.extra.dataRace = none := entry.noClocks
  have frameTracked : frame.extra.borrowTracker = some (borrow entry.choice) := entry.tracked
  have returnPlace : frame.returnPlace = p.destination := entry.returnPlace
  have varargs : frame.vaList = #[] := entry.varargs
  have continuation : frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind) := entry.continuation
  obtain ⟨older,original⟩ := Array.back?_eq_some_iff.mp input.current
  let room := ConcreteProtection.tag_room s p input resources
  let canonical := CanonicalInit.initializedMachine s p frame entry.previous input.tracker room
  have machineEq : entry.machine = entered entry.choice
      (FrameRelevance.pushedMachine p.before.stack.frames frame entry.previous
        (s.cfg.lifecycle.freshLocalsIdentity p.before.machine).1) := entry.machineEq
  have controlEq : entry.machine.user.payload.payload.user.host.control =
      p.before.machine.user.payload.payload.user.host.control := by
    rw [machineEq]
    cases entry.choice <;> change canonical.user.payload.payload.user.host.control = _
    all_goals exact initialized_control s metadata positive p frame entry.previous input.tracker room
  have fixed : entry.machine.threads.fixedScheduling = true := by
    rw [machineEq]
    cases entry.choice <;> change canonical.threads.fixedScheduling = true
    all_goals rw [initialized_fixed s metadata positive]; exact runtime.fixedScheduling
  obtain ⟨thread,activeCanonical⟩ := initialized_active s metadata positive p frame entry.previous input.tracker room
    input.thread input.active
  have gc : entry.machine.user.payload.payload.user.host.control.gcInterval = 0 := by rw [controlEq];exact runtime.gc
  have unchecked : entry.machine.user.payload.payload.user.host.control.checkedArithmetic = false := by rw [controlEq];exact runtime.unchecked
  let post := (TerminatorStep.after middle).machine
  let base := (TerminatorStep.after (LocalUnit.current p.before.stack.frames frame canonical)).machine
  have baseTracked : base.borrowTracker = some (UnitRetag.allocatedTracker input.tracker room) := rfl
  have baseActive : base.threads.activeThread? = some thread := activeCanonical
  have hook := TerminatorStep.canonical s metadata positive middle fixed gc unchecked
  have hookEq : (ExecutionMachine.stepHooks s.cfg s.limits).beforeTerminator () middle =
      (LocalUnit.current p.before.stack.frames frame post,.ok ()) := hook
  let ended := released entry.choice base
  let finalMachine := FrameExit.afterRelevanceAt (older.push input.caller) frame ended
    (thread.topUserRelevantFrame.getD (older.push input.caller).size)
  let finish := ReturnContinuation.resume older input.caller finalMachine p.returnBlock
  have popped : (ReturnStep.control s).popFrame () (LocalUnit.current (older.push input.caller) frame post) =
      ((⟨⟨older.push input.caller⟩,finalMachine⟩ : State),.ok frame) := by
    cases choiceEq : entry.choice with
    | miss =>
      have tracked : frame.extra.borrowTracker = some {} := by simpa [choiceEq,borrow] using frameTracked
      have postEq : post = base := by dsimp only [post,base,middle];rw [machineEq,choiceEq];rfl
      have popping := ReturnStep.pop s (older.push input.caller) frame base
        (UnitRetag.allocatedTracker input.tracker room) baseTracked tracked thread baseActive
      simpa only [finalMachine,ended,released,choiceEq,postEq] using popping
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
        unfold base canonical TerminatorStep.after CanonicalInit.initializedMachine UnitRetag.allocatedMachine FrameRelevance.pushedMachine
        rw [fields.freshLocalsIdentity]
        split <;> rfl
      have popping := ReturnNondata.pop s metadata positive (older.push input.caller) emptyBase base input.tracker room
        baseTracked input.world.globals p id registry memory thread baseActive
      rw [registered,←postEq] at popping
      simpa only [finalMachine,ended,released,choiceEq] using popping
    | live id old live tree release rights =>
      let emptyBase := {frame with extra := {frame.extra with borrowTracker := some {}}}
      have registered : UnitRetag.registeredFrame emptyBase {} id input.tracker.global.nextPointerTag = frame := by
        change {frame with extra := {frame.extra with borrowTracker := some {protectedTags := #[(id,input.tracker.global.nextPointerTag)]}}} = frame
        have tracked : frame.extra.borrowTracker = some {protectedTags := #[(id,input.tracker.global.nextPointerTag)]} := by simpa only [choiceEq,borrow] using frameTracked
        rw [←tracked]
      have postEq : post = {UnitRetag.registeredMachine base (UnitRetag.allocatedTracker input.tracker room)
          input.tracker.global.nextPointerTag with memory := UnitRetag.replaceTree base.memory id old tree} := by
        dsimp only [post,base,middle];rw [machineEq,choiceEq];rfl
      have popping := ReturnSingleton.pop s metadata positive (older.push input.caller) emptyBase base input.tracker room
        baseTracked input.world.globals id old tree release thread baseActive
      rw [registered,←postEq] at popping
      simpa only [finalMachine,ended,released,choiceEq] using popping
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
  have returned := ReturnSingleton.core_from_pop s metadata profile remaining capacity validation older input.caller
    frame post finalMachine body location locals noClocks popped destination.place
    (returnPlace.trans destination.encoding) destination.layout destination.sizedMetadata destination.alignmentCache
    p.returnBlock unwind normalCont varargs ghostPost shallowPost
  have returnEq : (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame () false
      (LocalUnit.current p.before.stack.frames frame post) = (finish,.ok ()) := by
    simpa only [original] using returned
  have second := ReturnStep.compose s metadata p.before.stack.frames frame entry.machine post finish body location hookEq returnEq
  have outside : finish.stack.frames.size < depth p := by simp [finish,ReturnContinuation.resume,depth,original]
  have inside : depth p ≤ middle.stack.frames.size := by simp [depth,middle,LocalUnit.current]
  have trace : Executes s (depth p) installed finish :=
    Executes.next (by omega) first (Executes.next inside second (Executes.refl _))
  have returnedToCaller : Returned p finish := by
    refine ⟨?_,?_,input.caller,{input.caller with location := .mir ⟨p.returnBlock,0⟩},input.current,?_,rfl,rfl,rfl,rfl,rfl⟩
    · simp [finish,ReturnContinuation.resume,original]
    · simp [finish,ReturnContinuation.resume,original]
    · simp [finish,ReturnContinuation.resume,Stack.currentFrame?]
  have safe := two_step_noErrors s (depth p) installed middle finish first second outside
  have preserved : Preservation.Preserves s p finish := by
    cases choiceEq : entry.choice with
    | miss =>
      have eqFinal : finish = ReturnContinuation.resume older input.caller
          (IntegerPost.machine s p frame entry.previous input.tracker room
            (thread.topUserRelevantFrame.getD (older.push input.caller).size)) p.returnBlock := by
        simp only [finish,finalMachine,ended,released,choiceEq,IntegerPost.machine,base,canonical,original]
      rw [eqFinal]
      exact IntegerPost.preserves s metadata positive p frame entry.previous input.tracker room _ older input.caller
        original input.world.enabled destination.place destination.encoding
    | nondata id registry =>
      have eqFinal : finish = ReturnContinuation.resume older input.caller
          (IntegerPost.machine s p frame entry.previous input.tracker room
            (thread.topUserRelevantFrame.getD (older.push input.caller).size)) p.returnBlock := by
        simp only [finish,finalMachine,ended,released,choiceEq,IntegerPost.machine,base,canonical,original]
      rw [eqFinal]
      exact IntegerPost.preserves s metadata positive p frame entry.previous input.tracker room _ older input.caller
        original input.world.enabled destination.place destination.encoding
    | live id old present tree released rights =>
      have eqFinal : finish = ReturnContinuation.resume older input.caller
          (ConcretePost.machine s p frame entry.previous input.tracker room
            (thread.topUserRelevantFrame.getD (older.push input.caller).size) id old tree) p.returnBlock := by
        simp only [finish,finalMachine,ended,WildcardEndpoint.released,choiceEq,ConcretePost.machine,IntegerPost.machine]
        congr 2
        unfold base canonical
        rw [original]
        unfold FrameExit.afterRelevanceAt FrameExit.afterRelevance
        split <;> rfl
      rw [eqFinal]
      exact ConcretePost.preserves s metadata positive p frame entry.previous input.tracker room _ older input.caller
        original input.world.enabled destination.place destination.encoding id old present tree rights
  exact ⟨installed,finish,entry.installed,depthEq,trace,returnedToCaller,preserved,safe,ScopedSafety.noUB_of_noErrors safe⟩
end EmptyFunction.WildcardEndpoint
