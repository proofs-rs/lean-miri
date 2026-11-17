import duplicate_prefix.PtrMetadataReturn
import duplicate_prefix.ActualPopPlan
namespace DuplicatePrefix.LenReturn
noncomputable section
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Concurrency
open PtrMetadataExecution PtrMetadataReturn
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem driver_with_plan
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (len : UInt64)
    (sourceBody : frame.body = HelperCompilerFacts.lenBody.body)
    (location : frame.location = .mir ⟨1,1⟩)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))))
    (cached0 : frame.locals[0].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace = none)
    (callerLocal : MIR.LocalId)
    (callerValid0 : (callerLocal : Miri.MIR.LocalId) < caller.locals.size)
    (callerLive0 : caller.locals[callerLocal].value = .live (.immediate .uninit))
    (callerCached0 : caller.locals[callerLocal].layout = some RootCompilerFacts.usizeLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller callerLocal RootCompilerFacts.usizeLayout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (finalMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory finalMemory)
    (thread : ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ControlFlow.returnFromCurrentFrame (GenericCallReturn.sourceControl config limits) () false
      (Storage.withCurrent (frames.push caller) frame machine) =
      (Storage.withCurrent frames
        {writeFrame caller callerLocal (.scalar (.fromScalarInt (.ofUInt64 len))) callerValid0 with location := .mir ⟨target,0⟩}
        (poppedMachine frames caller frame (ActualPopPlan.released machine finalMemory tracker borrowFrame) (thread.topUserRelevantFrame.getD (frames.push caller).size)),.ok ()) := by
  let index := thread.topUserRelevantFrame.getD (frames.push caller).size
  have top := GenericPopFrame.top_nonempty (frames.push caller) frame thread.topUserRelevantFrame
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let control := GenericCallReturn.sourceControl config limits
  let before := Storage.withCurrent (frames.push caller) frame machine
  let popped := poppedMachine frames caller frame (ActualPopPlan.released machine finalMemory tracker borrowFrame) index
  let afterPop := Storage.withCurrent frames caller popped
  let written := writeFrame caller callerLocal (.scalar (.fromScalarInt (.ofUInt64 len))) callerValid0
  let afterCopy := Storage.withCurrent frames written popped
  let result : OpTy Provenance := ⟨.immediate (.scalar (.fromScalarInt (.ofUInt64 len))),RootCompilerFacts.usizeLayout⟩
  let block := HelperCompilerFacts.lenBody.body.basicBlocks[1]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[1]? = some block := by rw [sourceBody];simp [block]
  have normal : block.cleanup = false := by with_unfolding_all rfl
  have read' : control.returnOperand () before = (before,.ok result) := by
    exact PrimitiveCallReturn.read_current_return options limits (remaining+1) span
      (frames.push caller) frame machine RootCompilerFacts.usizeLayout
      (.scalar (.fromScalarInt (.ofUInt64 len))) valid0 live0 cached0 ActualScalarCopy.usize_sized noClocks ghost
  have pop : control.popFrame () before = (afterPop,.ok frame) := by
    exact ActualPopPlan.pop_of_plan options limits (remaining+1) span (frames.push caller) frame machine tracker borrowFrame tracked frameTracked
      finalMemory plan thread active
  have copy : control.copyReturn () result frame.returnPlace afterPop = (afterCopy,.ok ()) := by
    have source := PrimitiveCallReturn.copy_usize_return options limits remaining span debugOff fuel validationFuel
      frames caller popped callerLocal .uninit len callerValid0 callerLive0 callerCached0 callerClocks
      (by rw [popped_user];exact ghost) (by rw [popped_user];exact shallow) frame.returnPlace destination
    simpa only [control,config,result,afterPop,afterCopy,written,writeFrame] using source
  have cleanup := PrimitiveCallReturn.cleanup_immediate_return options limits (remaining+1) span () afterCopy frame
    (some target) unwindAction continuation immediateLocals varargs
  have returned := GenericCallReturn.normal_goto control () before before afterPop afterCopy afterCopy frame frame
    ⟨1,1⟩ block result target unwindAction
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) location blockAt normal read' pop copy cleanup continuation
  change ControlFlow.returnFromCurrentFrame control () false before = _
  rw [returned]
  exact GenericCallReturn.goto_current frames written popped target

theorem step_with_plan
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (len : UInt64)
    (sourceBody : frame.body = HelperCompilerFacts.lenBody.body)
    (location : frame.location = .mir ⟨1,1⟩)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))))
    (cached0 : frame.locals[0].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : frame.extra.dataRace = none)
    (callerLocal : MIR.LocalId)
    (callerValid0 : (callerLocal : Miri.MIR.LocalId) < caller.locals.size)
    (callerLive0 : caller.locals[callerLocal].value = .live (.immediate .uninit))
    (callerCached0 : caller.locals[callerLocal].layout = some RootCompilerFacts.usizeLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller callerLocal RootCompilerFacts.usizeLayout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (finalMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory finalMemory)
    (thread : ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ExecutionMachine.step config limits ()
      (Storage.withCurrent (frames.push caller) frame machine) =
      (Storage.withCurrent frames
        {writeFrame caller callerLocal (.scalar (.fromScalarInt (.ofUInt64 len))) callerValid0 with location := .mir ⟨target,0⟩}
        (poppedMachine frames caller frame (ActualPopPlan.released (accountedMachine options remaining span machine) finalMemory tracker borrowFrame) (thread.topUserRelevantFrame.getD (frames.push caller).size)),.ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let before := Storage.withCurrent (frames.push caller) frame machine
  let next := accountedMachine options remaining span machine
  let nextState := Storage.withCurrent (frames.push caller) frame next
  have nextTracked : next.borrowTracker = some tracker := tracked
  have nextActive : next.threads.activeThread? = some thread := active
  have nextGhost : next.user.payload.ghost = false := by rw [accounted_ghost];exact ghost
  have nextValidation : next.user.payload.validation = .Shallow := by rw [accounted_validation];exact shallow
  have returned := driver_with_plan options limits remaining span debugOff fuel validationFuel frames caller frame next len
    sourceBody location valid0 live0 cached0 noClocks callerLocal callerValid0 callerLive0 callerCached0 callerClocks destination
    target unwindAction continuation immediateLocals varargs tracker borrowFrame nextTracked frameTracked finalMemory plan thread nextActive nextGhost nextValidation
  have accounting := SourceControl.before_terminator config limits () before
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks config limits).beforeTerminator () before = (nextState,.ok ()) := accounting
  let block := HelperCompilerFacts.lenBody.body.basicBlocks[1]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[1]? = some block := by rw [sourceBody];simp [block]
  have noStatement : block.statements[1]? = none := by with_unfolding_all rfl
  have kind : block.terminator.kind = .Return := by with_unfolding_all rfl
  exact GenericCallReturn.return_step_exact config limits () before nextState _ frame ⟨1,1⟩ block
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) location blockAt noStatement kind accounting' returned

end
end DuplicatePrefix.LenReturn
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.LenReturn.driver_with_plan, ``DuplicatePrefix.LenReturn.step_with_plan] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved actual protected len Return dependency {dependency}"
