import empty_function.LatentReturnPost
import empty_function.TerminatorStep
namespace EmptyFunction.LatentExecution
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Configuration EmptyFunction.Specification UnitRetag
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

private theorem prefixes (s : Static) (depth : Nat) (start middle finish : State)
    (first : ExecutionMachine.step s.cfg s.limits () start = (middle,.ok true))
    (second : ExecutionMachine.step s.cfg s.limits () middle = (finish,.ok true))
    (outside : finish.stack.frames.size < depth) :
    ScopedSafety.NoErrors s.cfg s.limits (fun _ _ => True) depth start := by
  apply ScopedSafety.noErrors_of_invariant (fun state => state = start ∨ state = middle ∨ state = finish)
  · exact Or.inl rfl
  · intro before after choice phase inside permitted step
    cases choice
    rcases phase with rfl | rfl | rfl
    · rw [first] at step; cases step; exact Or.inr (Or.inl rfl)
    · rw [second] at step; cases step; exact Or.inr (Or.inr rfl)
    · omega
  · intro state phase inside choice permitted
    cases choice
    rcases phase with rfl | rfl | rfl
    · exact ⟨middle,true,first⟩
    · exact ⟨finish,true,second⟩
    · omega

/-- Internal assembly after lazy protection. Its initial-operation equation is
provided by the actual raw initialization adapter, not an input validity field. -/
theorem run (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p) (resources : ResourceMargins s p)
    (destination : InputDraft.MemoryDestination s p input.tracker)
    (globals : GlobalAllocationHooks Provenance BorrowTree MiriMemoryKind
      (PlaceMachine.AccessState MiriMemoryKind RootUser))
    (binding : s.cfg.retag.ensureTreeExtra = GlobalAllocationMachine.ensure .global globals)
    (synchronize : ∀ memory view, globals.synchronizeMemory memory view = {view with machine := {view.machine with memory}})
    (frame : LocalUnit.F) (machine : ChoiceExecution.S) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (entry : InputDraft.Entry) (tree : BorrowTree)
    (protectedEq : tracker.global.protectedTags = input.tracker.global.protectedTags.insert input.tracker.global.nextPointerTag .StrongProtector)
    (released : tree.releaseProtector input.tracker.global.nextPointerTag tracker.global.protectedTags = ⟨tree,.Released⟩)
    (body : frame.body = s.loaded.body) (identity : frame.bodyIdentity = s.loaded.identity)
    (function : frame.functionInstance = s.functionInstance) (location : frame.location = .mir .start)
    (locals : frame.locals = #[{value := .live (.immediate .uninit),layout := none}])
    (noClocks : frame.extra.dataRace = none) (returnPlace : frame.returnPlace = p.destination)
    (continuation : frame.returnContinuation = CanonicalInit.normalizedContinuation s (.goto (some p.returnBlock) p.unwind))
    (varargs : frame.vaList = #[])
    (noGhost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (fixed : machine.threads.fixedScheduling = true)
    (gc : machine.user.payload.payload.user.host.control.gcInterval = 0)
    (unchecked : machine.user.payload.payload.user.host.control.checkedArithmetic = false)
    (thread : Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (initialized : WholeCall.install s p = .ok ()
      (LocalUnit.current p.before.stack.frames (registeredFrame frame {} id input.tracker.global.nextPointerTag)
        {machine with memory := replaceTree machine.memory id entry tree})) :
    let initial := LocalUnit.current p.before.stack.frames
      (registeredFrame frame {} id input.tracker.global.nextPointerTag)
      {machine with memory := replaceTree machine.memory id entry tree}
    let nextFrame := {BodyStep.withUnit (registeredFrame frame {} id input.tracker.global.nextPointerTag)
      .uninit (some s.abi.ret.layout) with location := .mir ⟨0,1⟩}
    let postMachine := (TerminatorStep.after initial).machine
    let releasedMachine := {postMachine with borrowTracker := some {tracker with global := {tracker.global with protectedTags := input.tracker.global.protectedTags}}}
    ∃ older,
      p.before.stack.frames = older.push input.caller ∧
      let finish := ReturnContinuation.resume older input.caller
        (FrameExit.afterRelevanceAt p.before.stack.frames nextFrame releasedMachine
          (thread.topUserRelevantFrame.getD p.before.stack.frames.size)) p.returnBlock
      WholeCall.install s p = .ok () initial ∧ initial.stack.frames.size = depth p ∧
      Executes s (depth p) initial finish ∧ Returned p finish ∧
      ScopedSafety.NoErrors s.cfg s.limits (fun _ _ => True) (depth p) initial ∧
      ScopedSafety.NoUB s.cfg s.limits (fun _ _ => True) (depth p) initial := by
  dsimp only
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  have positive : 0 < s.capacity := by have bound := resources.capacity; omega
  obtain ⟨remaining,capacity⟩ : ∃ n : Nat, s.capacity = n+2 :=
    ⟨s.capacity-2,by have bound := resources.capacity; omega⟩
  have validation : 0 < s.options.limits.validation := by have bound := resources.configuredValidation; omega
  let registered := registeredFrame frame {} id input.tracker.global.nextPointerTag
  let changed := {machine with memory := replaceTree machine.memory id entry tree}
  let initial := LocalUnit.current p.before.stack.frames registered changed
  let nextBase := {BodyStep.withUnit frame .uninit (some s.abi.ret.layout) with location := .mir ⟨0,1⟩}
  let nextFrame := registeredFrame nextBase {} id input.tracker.global.nextPointerTag
  let middle := LocalUnit.current p.before.stack.frames nextFrame changed
  have same : BodyStep.withUnit registered .uninit none = registered := by
    change {registered with locals := #[{value := .live (.immediate .uninit),layout := none}]} = registered
    dsimp only [registered,registeredFrame]
    rw [←locals]
  have first := BodyAssignment.step s metadata profile remaining capacity validation p.before.stack.frames registered changed
    identity body function location noClocks noGhost shallow
  rw [same] at first
  have firstEq : ExecutionMachine.step s.cfg s.limits () initial = (middle,.ok true) := first
  let basePost := (TerminatorStep.after (LocalUnit.current p.before.stack.frames nextBase machine)).machine
  let post := {basePost with memory := replaceTree basePost.memory id entry tree}
  let releasedMachine := {post with borrowTracker := some {tracker with global := {tracker.global with protectedTags := input.tracker.global.protectedTags}}}
  have hook := TerminatorStep.canonical s metadata positive middle fixed gc unchecked
  have hookEq : (ExecutionMachine.stepHooks s.cfg s.limits).beforeTerminator () middle =
      (LocalUnit.current p.before.stack.frames nextFrame post,.ok ()) := hook
  have popped := LatentReturnPost.pop s globals binding synchronize p.before.stack.frames nextBase basePost tracker enabled
    input.tracker.global.protectedTags input.tracker.global.nextPointerTag input.world.globals.nextNotProtected protectedEq
    id entry tree released thread active
  obtain ⟨older,original⟩ := Array.back?_eq_some_iff.mp input.current
  let finalMachine := FrameExit.afterRelevanceAt p.before.stack.frames nextFrame releasedMachine
    (thread.topUserRelevantFrame.getD p.before.stack.frames.size)
  let finish := ReturnContinuation.resume older input.caller finalMachine p.returnBlock
  have poppedEq : (ReturnStep.control s).popFrame () (LocalUnit.current (older.push input.caller) nextFrame post) =
      ((⟨⟨older.push input.caller⟩,finalMachine⟩ : State),.ok nextFrame) := by
    simpa only [finalMachine,nextFrame,releasedMachine,post,original] using popped
  have ghostPost : finalMachine.user.payload.ghost = false := by
    unfold finalMachine FrameExit.afterRelevanceAt FrameExit.afterRelevance
    split <;> exact noGhost
  have shallowPost : finalMachine.user.payload.validation = .Shallow := by
    unfold finalMachine FrameExit.afterRelevanceAt FrameExit.afterRelevance
    split <;> exact shallow
  obtain ⟨unwind,normalCont⟩ : ∃ unwind, nextFrame.returnContinuation = .goto (some p.returnBlock) unwind := by
    change ∃ unwind, frame.returnContinuation = .goto (some p.returnBlock) unwind
    rw [continuation]
    unfold CanonicalInit.normalizedContinuation
    split <;> exact ⟨_,rfl⟩
  have returned := ReturnSingleton.core_from_pop s metadata profile remaining capacity validation older input.caller
    nextFrame post finalMachine body rfl rfl noClocks poppedEq destination.place
    (returnPlace.trans destination.encoding) destination.layout destination.sizedMetadata destination.alignmentCache
    p.returnBlock unwind normalCont varargs ghostPost shallowPost
  have returnEq : (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame () false
      (LocalUnit.current p.before.stack.frames nextFrame post) = (finish,.ok ()) := by
    simpa only [original] using returned
  have second := ReturnStep.compose s metadata p.before.stack.frames nextFrame changed post finish body rfl hookEq returnEq
  have outside : finish.stack.frames.size < depth p := by simp [finish,ReturnContinuation.resume,depth,original]
  have inside : depth p ≤ middle.stack.frames.size := by simp [middle,depth,LocalUnit.current]
  have trace : Executes s (depth p) initial finish :=
    Executes.next (by simp [initial,depth,LocalUnit.current]) firstEq (Executes.next inside second (Executes.refl _))
  have returnedToCaller : Returned p finish := by
    refine ⟨?_,?_,input.caller,{input.caller with location := .mir ⟨p.returnBlock,0⟩},input.current,?_,rfl,rfl,rfl,rfl,rfl⟩
    · simp [finish,ReturnContinuation.resume,original]
    · simp [finish,ReturnContinuation.resume,original]
    · simp [finish,ReturnContinuation.resume,Stack.currentFrame?]
  have safe := prefixes s (depth p) initial middle finish firstEq second outside
  exact ⟨older,original,initialized,by simp [initial,depth,LocalUnit.current],trace,returnedToCaller,safe,ScopedSafety.noUB_of_noErrors safe⟩
end EmptyFunction.LatentExecution
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.LatentExecution." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved latent execution axiom {dependency} in {name}"
