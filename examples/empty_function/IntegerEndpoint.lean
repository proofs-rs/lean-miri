import empty_function.CanonicalInit
import empty_function.BodyAssignment
import empty_function.TerminatorStep
import empty_function.ReturnStep
import empty_function.IntegerPost
namespace EmptyFunction.IntegerEndpoint
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

 theorem init_body (s : Static) (metadata : Metadata s) [SuccessfulConstant metadata] (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p)
    (destination : InputDraft.MemoryDestination s p input.tracker)
    (integer : destination.place.mplace.ptr.provenance = none) :
    ∃ installed frame machine,
      WholeCall.install s p = .ok () installed ∧ installed.stack.frames.size = WholeCall.depth p ∧
      ExecutionMachine.step s.cfg s.limits () installed =
        (LocalUnit.current p.before.stack.frames frame machine,.ok true) ∧
      Meaning.FrameMatches frame s.loaded ∧ frame.bodyIdentity = s.loaded.identity ∧
      frame.functionInstance = s.functionInstance ∧ frame.location = .mir ⟨0,1⟩ ∧
      frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}] ∧
      frame.extra.borrowTracker = some {} ∧ frame.extra.dataRace = none ∧
      frame.returnPlace = p.destination ∧
      frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind) ∧
      frame.vaList = #[] ∧ machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
      ∃ (previous : LocalUnit.F) (room : input.tracker.global.nextPointerTag.value < 18446744073709551615),
        machine = CanonicalInit.initializedMachine s p frame previous input.tracker room := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  obtain ⟨remaining,capacity⟩ : ∃ n : Nat, s.capacity = n+2 :=
    ⟨s.capacity-2,by have bound := resources.capacity; omega⟩
  have validation : 0 < s.options.limits.validation := by
    have bound := resources.configuredValidation
    omega
  obtain ⟨entry,machine,installed,body,identity,function,location,locals,tracked,noClocks,returnPlace,
    continuation,varargs,noGhost,shallow,previous,room,machineEq⟩ :=
      CanonicalInit.init_integer s metadata profile p runtime input resources destination integer
  have entrySame : BodyStep.withUnit entry .uninit none = entry := by
    change {entry with locals := #[{value := .live (.immediate .uninit),layout := none}]} = entry
    rw [←locals]
  have bodyStep := BodyAssignment.step s metadata profile remaining capacity validation p.before.stack.frames entry
    machine identity body function location noClocks noGhost shallow
  rw [entrySame] at bodyStep
  let next := {(BodyStep.withUnit entry .uninit (some s.abi.ret.layout)) with location := .mir ⟨0,1⟩}
  refine ⟨LocalUnit.current p.before.stack.frames entry machine,next,machine,installed,?_,bodyStep,?_,?_,?_,?_,?_,
    ?_,?_,?_,?_,?_,noGhost,shallow,previous,room,?_⟩
  · simp [LocalUnit.current,WholeCall.depth]
  all_goals try rfl
  all_goals try simpa only [Meaning.FrameMatches,next,BodyStep.withUnit,LocalUnit.withUnit] using body
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

private theorem old_rights_refl (tree : Miri.TreeBorrows.BorrowTree) :
    Preservation.OldNodeRights tree tree := by
  refine ⟨?_,?_,?_⟩
  · intro tag index found; exact found
  · intro root member; exact member
  · intro index old found
    refine ⟨old,found,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
    · intro child member; exact member
    · intro byte segment member contains
      exact ⟨segment,member,contains,rfl,rfl⟩
private theorem original_live_of_memory (before after : State)
    (same : after.machine.memory = before.machine.memory) :
    Preservation.OriginalLiveAllocations before after := by
  intro id old found
  refine ⟨old,?_,rfl,rfl,old_rights_refl _⟩
  simpa only [same] using found
private theorem address_facts_refl (state : State) : Preservation.ExistingAddressFacts state state := by
  refine ⟨rfl,rfl,?_,?_,?_⟩
  · intro id row found; exact found
  · intro row member; exact ⟨row,member,rfl,rfl⟩
  · intro id member
    exact Array.contains_iff_mem.mpr member

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

 theorem result (s : Static) (metadata : Metadata s) [SuccessfulConstant metadata] (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p)
    (destination : InputDraft.MemoryDestination s p input.tracker)
    (integer : destination.place.mplace.ptr.provenance = none) :
    WholeCall.Result s (Preservation.Preserves s) p := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  have positive : 0 < s.capacity := by have bound := resources.capacity; omega
  obtain ⟨remaining,capacity⟩ : ∃ n : Nat, s.capacity = n+2 :=
    ⟨s.capacity-2,by have bound := resources.capacity; omega⟩
  have validation : 0 < s.options.limits.validation := by have bound := resources.configuredValidation; omega
  obtain ⟨installed,frame,machine,installEq,depthEq,first,body,identity,function,location,locals,frameTracked,
    noClocks,returnPlace,continuation,varargs,noGhost,shallow,previous,room,machineEq⟩ :=
      init_body s metadata profile p runtime input resources destination integer
  have current : p.before.stack.frames.back? = some input.caller := input.current
  obtain ⟨older,original⟩ := Array.back?_eq_some_iff.mp current
  have controlEq : machine.user.payload.payload.user.host.control =
      p.before.machine.user.payload.payload.user.host.control := by
    rw [machineEq]
    exact initialized_control s metadata positive p frame previous input.tracker room
  have fixed : machine.threads.fixedScheduling = true := by
    rw [machineEq, initialized_fixed s metadata positive]
    exact runtime.fixedScheduling
  have gc : machine.user.payload.payload.user.host.control.gcInterval = 0 := by rw [controlEq]; exact runtime.gc
  have unchecked : machine.user.payload.payload.user.host.control.checkedArithmetic = false := by
    rw [controlEq]; exact runtime.unchecked
  obtain ⟨thread,active⟩ := initialized_active s metadata positive p frame previous input.tracker room
    input.thread input.active
  rw [←machineEq] at active
  let post := (TerminatorStep.after (LocalUnit.current p.before.stack.frames frame machine)).machine
  have hook := TerminatorStep.canonical s metadata positive
    (LocalUnit.current p.before.stack.frames frame machine) fixed gc unchecked
  have hookEq : (ExecutionMachine.stepHooks s.cfg s.limits).beforeTerminator ()
      (LocalUnit.current p.before.stack.frames frame machine) =
      (LocalUnit.current p.before.stack.frames frame post,.ok ()) := hook
  have tracked : post.borrowTracker = some (UnitRetag.allocatedTracker input.tracker room) := by
    change machine.borrowTracker = _
    rw [machineEq]
    rfl
  have activePost : post.threads.activeThread? = some thread := active
  have ghostPost : post.user.payload.ghost = false := noGhost
  have shallowPost : post.user.payload.validation = .Shallow := shallow
  obtain ⟨unwind,normalCont⟩ : ∃ unwind,
      frame.returnContinuation = .goto (some p.returnBlock) unwind := by
    rw [continuation]
    unfold CanonicalInit.normalizedContinuation
    split <;> exact ⟨_,rfl⟩
  let finishedMachine := FrameExit.afterRelevanceAt (older.push input.caller) frame post
    (thread.topUserRelevantFrame.getD (older.push input.caller).size)
  let finish := ReturnContinuation.resume older input.caller finishedMachine p.returnBlock
  have returned := ReturnStep.core s metadata profile remaining capacity validation older input.caller frame post
    body location locals noClocks frameTracked (UnitRetag.allocatedTracker input.tracker room) tracked
    thread activePost destination.place (returnPlace.trans destination.encoding) destination.layout
    destination.sizedMetadata destination.alignmentCache p.returnBlock unwind normalCont varargs ghostPost shallowPost
  have returnEq : (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame () false
      (LocalUnit.current p.before.stack.frames frame post) = (finish,.ok ()) := by
    simpa only [original,BodyStep.current,LocalUnit.current] using returned
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
  have preserved := IntegerPost.preserves s metadata positive p frame previous input.tracker room
    (thread.topUserRelevantFrame.getD (older.push input.caller).size) older input.caller original
    input.world.enabled destination.place destination.encoding
  have preservedFinish : Preservation.Preserves s p finish := by
    simpa only [finish,finishedMachine,post,IntegerPost.machine,original,machineEq] using preserved
  exact ⟨installed,finish,installEq,depthEq,trace,returnedToCaller,preservedFinish,safe,
    ScopedSafety.noUB_of_noErrors safe⟩
end EmptyFunction.IntegerEndpoint
