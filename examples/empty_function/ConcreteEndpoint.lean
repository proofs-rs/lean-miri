import empty_function.ConcreteInit
import empty_function.ReturnSingleton
import empty_function.TerminatorStep
namespace EmptyFunction.ConcreteEndpoint
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

/-- The common integer baseline, with only the selected tree replaced after release. -/
def releasedPost (s : Static) (p : Packet) (frame previous : LocalUnit.F)
    (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : InputDraft.Entry) (tree : BorrowTree) :=
  let base := (TerminatorStep.after (LocalUnit.current p.before.stack.frames frame
    (CanonicalInit.initializedMachine s p frame previous tracker room))).machine
  {base with memory := UnitRetag.replaceTree base.memory id entry tree}

def finishedMachine (s : Static) (p : Packet) (frame previous : LocalUnit.F)
    (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : InputDraft.Entry) (tree : BorrowTree) (index : Nat) :=
  FrameExit.afterRelevanceAt p.before.stack.frames frame
    (releasedPost s p frame previous tracker room id entry tree) index

 theorem init_body (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p)
    (destination : InputDraft.MemoryDestination s p input.tracker)
    (id : AllocId) (tag : BorTag)
    (encoding : destination.place.mplace.ptr.provenance = some (.concrete id tag))
    (entry : InputDraft.Entry)
    (live : p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    ∃ installed frame machine tree,
      WholeCall.install s p = .ok () installed ∧ installed.stack.frames.size = WholeCall.depth p ∧
      ExecutionMachine.step s.cfg s.limits () installed =
        (LocalUnit.current p.before.stack.frames frame machine,.ok true) ∧
      frame.body = s.loaded.body ∧ frame.bodyIdentity = s.loaded.identity ∧
      frame.functionInstance = s.functionInstance ∧ frame.location = .mir ⟨0,1⟩ ∧
      frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}] ∧
      frame.extra.borrowTracker = some {protectedTags := #[(id,input.tracker.global.nextPointerTag)]} ∧ frame.extra.dataRace = none ∧
      frame.returnPlace = p.destination ∧
      frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind) ∧
      frame.vaList = #[] ∧ machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
      (∃ previous, machine = ConcreteInit.initializedMachine s p frame previous input.tracker
        (ConcreteProtection.tag_room s p input resources) id entry tree) ∧
      tree.releaseProtector input.tracker.global.nextPointerTag
        (UnitRetag.registeredTracker
          (UnitRetag.allocatedTracker input.tracker (ConcreteProtection.tag_room s p input resources))
          input.tracker.global.nextPointerTag).global.protectedTags = ⟨tree,.Released⟩ ∧
      Preservation.OldNodeRights entry.allocation.extra tree := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  obtain ⟨remaining,capacity⟩ : ∃ n : Nat, s.capacity = n+2 :=
    ⟨s.capacity-2,by have bound := resources.capacity; omega⟩
  have validation : 0 < s.options.limits.validation := by
    have bound := resources.configuredValidation
    omega
  obtain ⟨entryFrame,machine,tree,installed,body,identity,function,location,locals,tracked,noClocks,returnPlace,
    continuation,varargs,noGhost,shallow,⟨previous,machineEq⟩,released,rights⟩ :=
      ConcreteInit.init_live s metadata profile metadata.pointerSize p runtime input resources destination id tag encoding entry live
  have entrySame : BodyStep.withUnit entryFrame .uninit none = entryFrame := by
    change {entryFrame with locals := #[{value := .live (.immediate .uninit),layout := none}]} = entryFrame
    rw [←locals]
  have bodyStep := BodyAssignment.step s metadata profile remaining capacity validation p.before.stack.frames entryFrame
    machine identity body function location noClocks noGhost shallow
  rw [entrySame] at bodyStep
  let next := {(BodyStep.withUnit entryFrame .uninit (some s.abi.ret.layout)) with location := .mir ⟨0,1⟩}
  refine ⟨LocalUnit.current p.before.stack.frames entryFrame machine,next,machine,tree,installed,?_,bodyStep,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,noGhost,shallow,⟨previous,?_⟩,released,rights⟩
  · simp [LocalUnit.current,WholeCall.depth]
  all_goals try rfl
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using body
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using identity
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using function
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using tracked
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using noClocks
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using returnPlace
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using continuation
  all_goals try simpa only [next,BodyStep.withUnit,LocalUnit.withUnit] using varargs
  rw [machineEq]
  rfl


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

 theorem run_operations (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p)
    (destination : InputDraft.MemoryDestination s p input.tracker)
    (id : AllocId) (tag : BorTag)
    (encoding : destination.place.mplace.ptr.provenance = some (.concrete id tag))
    (entry : InputDraft.Entry)
    (live : p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    ∃ (installed finish : State) (frame previous : LocalUnit.F) (tree : BorrowTree) (index : Nat)
      (older : Array LocalUnit.F),
      p.before.stack.frames = older.push input.caller ∧
      WholeCall.install s p = .ok () installed ∧ installed.stack.frames.size = depth p ∧
      Executes s (depth p) installed finish ∧ Returned p finish ∧
      ScopedSafety.NoErrors s.cfg s.limits (fun _ _ => True) (depth p) installed ∧
      ScopedSafety.NoUB s.cfg s.limits (fun _ _ => True) (depth p) installed ∧
      finish = ReturnContinuation.resume older input.caller
        (finishedMachine s p frame previous input.tracker (ConcreteProtection.tag_room s p input resources)
          id entry tree index) p.returnBlock ∧
      Preservation.OldNodeRights entry.allocation.extra tree := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  have positive : 0 < s.capacity := by have bound := resources.capacity; omega
  obtain ⟨remaining,capacity⟩ : ∃ n : Nat, s.capacity = n+2 :=
    ⟨s.capacity-2,by have bound := resources.capacity; omega⟩
  have validation : 0 < s.options.limits.validation := by have bound := resources.configuredValidation; omega
  obtain ⟨installed,frame,machine,tree,installEq,depthEq,first,body,identity,function,location,locals,frameTracked,
    noClocks,returnPlace,continuation,varargs,noGhost,shallow,⟨previous,machineEq⟩,released,rights⟩ :=
      init_body s metadata profile p runtime input resources destination id tag encoding entry live
  obtain ⟨older,original⟩ := Array.back?_eq_some_iff.mp input.current
  let room := ConcreteProtection.tag_room s p input resources
  let canonical := CanonicalInit.initializedMachine s p frame previous input.tracker room
  have controlEq : machine.user.payload.payload.user.host.control =
      p.before.machine.user.payload.payload.user.host.control := by
    rw [machineEq]
    change canonical.user.payload.payload.user.host.control = _
    exact initialized_control s metadata positive p frame previous input.tracker room
  have fixed : machine.threads.fixedScheduling = true := by
    rw [machineEq]
    change canonical.threads.fixedScheduling = true
    rw [initialized_fixed s metadata positive]
    exact runtime.fixedScheduling
  have gc : machine.user.payload.payload.user.host.control.gcInterval = 0 := by rw [controlEq]; exact runtime.gc
  have unchecked : machine.user.payload.payload.user.host.control.checkedArithmetic = false := by
    rw [controlEq]; exact runtime.unchecked
  obtain ⟨thread,activeCanonical⟩ := initialized_active s metadata positive p frame previous input.tracker room
    input.thread input.active
  have active : machine.threads.activeThread? = some thread := by
    rw [machineEq]
    exact activeCanonical
  let post := (TerminatorStep.after (LocalUnit.current p.before.stack.frames frame machine)).machine
  let base := (TerminatorStep.after (LocalUnit.current p.before.stack.frames frame canonical)).machine
  have baseTracked : base.borrowTracker = some (UnitRetag.allocatedTracker input.tracker room) := rfl
  have baseActive : base.threads.activeThread? = some thread := activeCanonical
  have hook := TerminatorStep.canonical s metadata positive
    (LocalUnit.current p.before.stack.frames frame machine) fixed gc unchecked
  have hookEq : (ExecutionMachine.stepHooks s.cfg s.limits).beforeTerminator ()
      (LocalUnit.current p.before.stack.frames frame machine) =
      (LocalUnit.current p.before.stack.frames frame post,.ok ()) := hook
  let emptyBase := {frame with extra := {frame.extra with borrowTracker := some {}}}
  have registered : UnitRetag.registeredFrame emptyBase {} id input.tracker.global.nextPointerTag = frame := by
    change {frame with extra := {frame.extra with borrowTracker := some {protectedTags := #[(id,input.tracker.global.nextPointerTag)]}}} = frame
    rw [←frameTracked]
  have postEq : post =
      {UnitRetag.registeredMachine base (UnitRetag.allocatedTracker input.tracker room)
        input.tracker.global.nextPointerTag with memory := UnitRetag.replaceTree base.memory id entry tree} := by
    dsimp only [post,base]
    rw [machineEq]
    rfl
  let releasedMachine := {base with memory := UnitRetag.replaceTree base.memory id entry tree}
  let finalMachine := FrameExit.afterRelevanceAt (older.push input.caller) frame releasedMachine
    (thread.topUserRelevantFrame.getD (older.push input.caller).size)
  let finish := ReturnContinuation.resume older input.caller finalMachine p.returnBlock
  have popped := ReturnSingleton.pop s metadata positive (older.push input.caller) emptyBase base input.tracker room
    baseTracked input.world.globals id entry tree released thread baseActive
  rw [registered,←postEq] at popped
  have ghostPost : finalMachine.user.payload.ghost = false := by
    unfold finalMachine FrameExit.afterRelevanceAt FrameExit.afterRelevance
    split <;> change canonical.user.payload.ghost = false
    all_goals rw [machineEq] at noGhost; exact noGhost
  have shallowPost : finalMachine.user.payload.validation = .Shallow := by
    unfold finalMachine FrameExit.afterRelevanceAt FrameExit.afterRelevance
    split <;> change canonical.user.payload.validation = .Shallow
    all_goals rw [machineEq] at shallow; exact shallow
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
  have second := ReturnStep.compose s metadata p.before.stack.frames frame machine post finish body location hookEq returnEq
  have outside : finish.stack.frames.size < depth p := by
    simp [finish,ReturnContinuation.resume,depth,original]
  have inside : depth p ≤ (LocalUnit.current p.before.stack.frames frame machine).stack.frames.size := by
    simp [depth,LocalUnit.current]
  have trace : Executes s (depth p) installed finish :=
    Executes.next (by omega) first (Executes.next inside second (Executes.refl _))
  have returnedToCaller : Returned p finish := by
    refine ⟨?_,?_,input.caller,{input.caller with location := .mir ⟨p.returnBlock,0⟩},input.current,?_,rfl,rfl,rfl,rfl,rfl⟩
    · simp [finish,ReturnContinuation.resume,original]
    · simp [finish,ReturnContinuation.resume,original]
    · simp [finish,ReturnContinuation.resume,Stack.currentFrame?]
  have safe := two_step_noErrors s (depth p) installed (LocalUnit.current p.before.stack.frames frame machine)
    finish first second outside
  refine ⟨installed,finish,frame,previous,tree,thread.topUserRelevantFrame.getD (older.push input.caller).size,
    older,original,installEq,depthEq,trace,returnedToCaller,safe,ScopedSafety.noUB_of_noErrors safe,?_,rights⟩
  simp only [finish,finalMachine,finishedMachine,releasedPost,releasedMachine,base,canonical,original]

end EmptyFunction.ConcreteEndpoint
