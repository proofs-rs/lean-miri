import empty_function.LocalModel
import empty_function.LocalReturn
import empty_function.LocalPost
namespace EmptyFunction.LocalEndpoint
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

 theorem init_body (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p) (destination : InputDraft.LocalDestination s p input.tracker)
    (whole : destination.offset = none) (value : Immediate Provenance)
    (immediate : destination.oldOperand = .immediate value) :
    ∃ (older : Array LocalUnit.F) (bound : destination.localId < destination.caller.locals.size)
      (installed : State) (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser),
      p.before.stack.frames = older.push destination.caller ∧
      WholeCall.install s p = .ok () installed ∧ installed.stack.frames.size = depth p ∧
      ExecutionMachine.step s.cfg s.limits () installed =
        (LocalUnit.current (older.push (LocalModel.caller s p input.tracker destination bound)) frame machine,.ok true) ∧
      frame.body = s.loaded.body ∧ frame.bodyIdentity = s.loaded.identity ∧
      frame.functionInstance = s.functionInstance ∧ frame.location = .mir ⟨0,1⟩ ∧
      frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}] ∧
      frame.extra.borrowTracker = some {} ∧ frame.extra.dataRace = none ∧ frame.returnPlace = p.destination ∧
      frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind) ∧
      frame.vaList = #[] ∧ machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
      (∃ previous, machine = LocalModel.initializedMachine s p input.tracker destination older bound frame previous) ∧
      machine.borrowTracker = p.before.machine.borrowTracker := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  obtain ⟨remaining,capacity⟩ : ∃ n : Nat, s.capacity = n+2 := ⟨s.capacity-2,by have bound := resources.capacity; omega⟩
  have validation : 0 < s.options.limits.validation := by have bound := resources.configuredValidation; omega
  obtain ⟨older,bound,entry,machine,original,installed,body,identity,function,location,locals,tracked,noClocks,
    returnPlace,continuation,varargs,noGhost,shallow,⟨previous,machineEq⟩,machineTracked⟩ :=
      LocalInit.init_whole s metadata profile p runtime input resources destination whole value immediate
  let frames := older.push (LocalModel.caller s p input.tracker destination bound)
  have entrySame : BodyStep.withUnit entry .uninit none = entry := by
    change {entry with locals := #[{value := .live (.immediate .uninit),layout := none}]} = entry
    rw [←locals]
  have first := BodyAssignment.step s metadata profile remaining capacity validation frames entry machine
    identity body function location noClocks noGhost shallow
  rw [entrySame] at first
  let next : LocalUnit.F := {(BodyStep.withUnit entry .uninit (some s.abi.ret.layout)) with location := .mir ⟨0,1⟩}
  refine ⟨older,bound,LocalUnit.current frames entry machine,next,machine,original,installed,?_,first,
    ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,noGhost,shallow,⟨previous,?_⟩,machineTracked⟩
  · simp [LocalUnit.current,frames,depth,original]
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

 theorem run_operations (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p) (destination : InputDraft.LocalDestination s p input.tracker)
    (whole : destination.offset = none) (value : Immediate Provenance)
    (immediate : destination.oldOperand = .immediate value) :
    ∃ (installed finish : State) (older : Array LocalUnit.F)
      (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) (index : Nat),
      p.before.stack.frames = older.push destination.caller ∧
      WholeCall.install s p = .ok () installed ∧ installed.stack.frames.size = depth p ∧
      Executes s (depth p) installed finish ∧ Returned p finish ∧
      ScopedSafety.NoErrors s.cfg s.limits (fun _ _ => True) (depth p) installed ∧
      ScopedSafety.NoUB s.cfg s.limits (fun _ _ => True) (depth p) installed ∧
      finish = LocalModel.finish s p input.tracker destination older bound frame previous index := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  have positive : 0 < s.capacity := by have bound := resources.capacity; omega
  obtain ⟨remaining,capacity⟩ : ∃ n : Nat, s.capacity = n+2 := ⟨s.capacity-2,by have bound := resources.capacity; omega⟩
  have validation : 0 < s.options.limits.validation := by have bound := resources.configuredValidation; omega
  obtain ⟨older,bound,installed,frame,machine,original,installEq,depthEq,first,body,identity,function,location,
    locals,frameTracked,noClocks,returnPlace,continuation,varargs,noGhost,shallow,⟨previous,machineEq⟩,tracked⟩ :=
      init_body s metadata profile p runtime input resources destination whole value immediate
  let caller := LocalModel.caller s p input.tracker destination bound
  let frames := older.push caller
  have controlEq : machine.user.payload.payload.user.host.control =
      p.before.machine.user.payload.payload.user.host.control := by
    rw [machineEq]
    exact initialized_control s metadata positive p input.tracker destination older bound frame previous
  have fixed : machine.threads.fixedScheduling = true := by
    rw [machineEq,initialized_fixed s metadata positive]
    exact runtime.fixedScheduling
  have gc : machine.user.payload.payload.user.host.control.gcInterval = 0 := by rw [controlEq]; exact runtime.gc
  have unchecked : machine.user.payload.payload.user.host.control.checkedArithmetic = false := by rw [controlEq]; exact runtime.unchecked
  obtain ⟨thread,active⟩ := initialized_active s metadata positive p input.tracker destination older bound frame previous
    input.thread input.active
  rw [←machineEq] at active
  let post := (TerminatorStep.after (LocalUnit.current frames frame machine)).machine
  have hook := TerminatorStep.canonical s metadata positive (LocalUnit.current frames frame machine) fixed gc unchecked
  have hookEq : (ExecutionMachine.stepHooks s.cfg s.limits).beforeTerminator ()
      (LocalUnit.current frames frame machine) = (LocalUnit.current frames frame post,.ok ()) := hook
  have trackedPost : post.borrowTracker = some input.tracker := tracked.trans input.world.enabled
  have activePost : post.threads.activeThread? = some thread := active
  have ghostPost : post.user.payload.ghost = false := noGhost
  have shallowPost : post.user.payload.validation = .Shallow := shallow
  have sameCaller : destination.caller = input.caller := Option.some.inj (destination.current.symm.trans input.current)
  have callerNoClocks : caller.extra.dataRace = none := by
    change destination.caller.extra.dataRace = none
    rw [sameCaller]
    exact input.callerNoClocks
  have atSlot : caller.locals[destination.localId]? = some {destination.slot with layout := some s.abi.ret.layout} :=
    LocalImmediate.cached_at destination.caller destination.localId destination.slot s.abi.ret.layout bound
  have live : ({destination.slot with layout := some s.abi.ret.layout} : LocalState Provenance LocalLayout).value =
      .live (.immediate .uninit) := by
    obtain ⟨_,valueEq⟩ := LocalPreflight.old_unit s metadata p input.tracker destination whole value immediate
    rw [valueEq] at immediate
    exact destination.live.trans (congrArg LocalValue.live immediate)
  have returnedPlace : frame.returnPlace = .frameLocal older.size destination.localId none s.abi.ret.layout caller.localsIdentity := by
    rw [returnPlace,destination.encoding,whole,original]
    simp [caller,LocalModel.caller,LocalImmediate.cached]
  obtain ⟨unwind,normalCont⟩ : ∃ unwind, frame.returnContinuation = .goto (some p.returnBlock) unwind := by
    rw [continuation]
    unfold CanonicalInit.normalizedContinuation
    split <;> exact ⟨_,rfl⟩
  let finalMachine := FrameExit.afterRelevanceAt frames frame post (thread.topUserRelevantFrame.getD frames.size)
  let finish := ReturnContinuation.resume older caller finalMachine p.returnBlock
  have returned := LocalReturn.core s metadata profile remaining capacity validation older caller frame post body location
    locals noClocks frameTracked input.tracker trackedPost thread activePost destination.localId _ atSlot live rfl
    callerNoClocks returnedPlace p.returnBlock unwind normalCont varargs ghostPost shallowPost
  have second := ReturnStep.compose s metadata frames frame machine post finish body location hookEq returned
  have outside : finish.stack.frames.size < depth p := by
    simp [finish,ReturnContinuation.resume,depth,original]
  have inside : depth p ≤ (LocalUnit.current frames frame machine).stack.frames.size := by
    simp [depth,LocalUnit.current,frames,original]
  have trace : Executes s (depth p) installed finish :=
    Executes.next (by omega) first (Executes.next inside second (Executes.refl _))
  have returnedToCaller : Returned p finish := by
    refine ⟨?_,?_,destination.caller,{caller with location := .mir ⟨p.returnBlock,0⟩},destination.current,?_,rfl,rfl,rfl,rfl,rfl⟩
    · simp [finish,ReturnContinuation.resume,original]
    · simp [finish,ReturnContinuation.resume,original]
    · simp [finish,ReturnContinuation.resume,Stack.currentFrame?]
  have safe := two_step_noErrors s (depth p) installed (LocalUnit.current frames frame machine) finish first second outside
  refine ⟨installed,finish,older,bound,frame,previous,thread.topUserRelevantFrame.getD frames.size,
    original,installEq,depthEq,trace,returnedToCaller,safe,ScopedSafety.noUB_of_noErrors safe,?_⟩
  simp only [finish,finalMachine,post,LocalModel.finish,LocalModel.machine,machineEq,frames,caller]

 theorem result (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p) (destination : InputDraft.LocalDestination s p input.tracker)
    (whole : destination.offset = none) (value : Immediate Provenance)
    (immediate : destination.oldOperand = .immediate value) :
    WholeCall.Result s (Preservation.Preserves s) p := by
  obtain ⟨installed,finish,older,bound,frame,previous,index,original,installEq,depthEq,execution,returned,noErrors,noUB,finishEq⟩ :=
    run_operations s metadata profile p runtime input resources destination whole value immediate
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  have positive : 0 < s.capacity := by have bound := resources.capacity; omega
  have preserved := LocalPost.preserves s metadata positive p input.tracker destination older bound frame previous index original whole
  rw [←finishEq] at preserved
  exact ⟨installed,finish,installEq,depthEq,execution,returned,preserved,noErrors,noUB⟩

end EmptyFunction.LocalEndpoint
