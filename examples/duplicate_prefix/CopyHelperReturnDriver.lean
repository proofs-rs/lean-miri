import duplicate_prefix.CopyHelperReturn
import duplicate_prefix.ActualPopPlan
import duplicate_prefix.PtrMetadataExecution
import duplicate_prefix.PtrMetadataReturn

namespace DuplicatePrefix.CopyHelperReturnDriver
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem return_driver
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (location : frame.location = .mir ⟨7,12⟩)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate .uninit))
    (uncached0 : frame.locals[0].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (callerId : MIR.LocalId) (callerValid : callerId < caller.locals.size)
    (callerOld : Immediate Provenance)
    (callerLive : caller.locals[callerId].value = .live (.immediate callerOld))
    (callerCached : caller.locals[callerId].layout = some CopyHelperUnit.layout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller callerId CopyHelperUnit.layout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (immediateLocals : ∀ slot ∈ (LocalOperands.cachedLayoutFrame frame 0 CopyHelperUnit.layout valid0).locals,
      ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (finalMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory finalMemory)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let cached := LocalOperands.cachedLayoutFrame frame 0 CopyHelperUnit.layout valid0
    let popped := GenericPopFrame.afterRelevanceAt (frames.push caller) cached
      (ActualPopPlan.released machine finalMemory tracker borrowFrame)
      (thread.topUserRelevantFrame.getD (frames.push caller).size)
    ControlFlow.returnFromCurrentFrame (GenericCallReturn.sourceControl config limits) () false
      (Storage.withCurrent (frames.push caller) frame machine) =
      (Storage.withCurrent frames
        {PtrMetadataExecution.writeFrame caller callerId .uninit callerValid with location := .mir ⟨target,0⟩}
        popped,.ok ()) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let control := GenericCallReturn.sourceControl config limits
  let cached := LocalOperands.cachedLayoutFrame frame 0 CopyHelperUnit.layout valid0
  let released := ActualPopPlan.released machine finalMemory tracker borrowFrame
  let popped := GenericPopFrame.afterRelevanceAt (frames.push caller) cached released
    (thread.topUserRelevantFrame.getD (frames.push caller).size)
  let before := Storage.withCurrent (frames.push caller) frame machine
  let afterRead := Storage.withCurrent (frames.push caller) cached machine
  let afterPop := Storage.withCurrent frames caller popped
  let written := PtrMetadataExecution.writeFrame caller callerId .uninit callerValid
  let afterCopy := Storage.withCurrent frames written popped
  let result : OpTy Provenance := ⟨.immediate .uninit,CopyHelperUnit.layout⟩
  let block := HelperCompilerFacts.copyBody.body.basicBlocks[7]'(by decide +kernel)
  have blockAt : frame.body.basicBlocks[7]? = some block := by rw [sourceBody];simp [block]
  have normal : block.cleanup = false := by decide +kernel
  have read' : control.returnOperand () before = (afterRead,.ok result) :=
    CopyHelperReturn.read_unit_return_uncached options limits (remaining+1) span (frames.push caller)
      frame machine sourceBody identity callee valid0 live0 uncached0 noClocks ghost
  have pop : control.popFrame () afterRead = (afterPop,.ok cached) := by
    exact ActualPopPlan.pop_of_plan options limits (remaining+1) span (frames.push caller) cached machine
      tracker borrowFrame tracked frameTracked finalMemory plan thread active
  have poppedUser : popped.user = machine.user := by
    unfold popped GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have copy : control.copyReturn () result cached.returnPlace afterPop = (afterCopy,.ok ()) := by
    exact CopyHelperReturn.copy_unit_return options limits remaining span debugOff fuel validationFuel
      frames caller popped callerId callerOld callerValid callerLive callerCached callerClocks
      (by rw [poppedUser];exact ghost) (by rw [poppedUser];exact shallow) cached.returnPlace destination
  have cleanup := PrimitiveCallReturn.cleanup_immediate_return options limits (remaining+1) span () afterCopy cached
    (some target) unwindAction continuation immediateLocals varargs
  have returned := GenericCallReturn.normal_goto control () before afterRead afterPop afterCopy afterCopy frame cached
    ⟨7,12⟩ block result target unwindAction
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) location blockAt normal read' pop copy cleanup continuation
  change ControlFlow.returnFromCurrentFrame control () false before = _
  rw [returned]
  exact GenericCallReturn.goto_current frames written popped target

theorem return_step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = HelperCompilerFacts.copyBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.copyBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.copyCall.callee)
    (location : frame.location = .mir ⟨7,12⟩)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate .uninit))
    (uncached0 : frame.locals[0].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (callerId : MIR.LocalId) (callerValid : callerId < caller.locals.size)
    (callerOld : Immediate Provenance)
    (callerLive : caller.locals[callerId].value = .live (.immediate callerOld))
    (callerCached : caller.locals[callerId].layout = some CopyHelperUnit.layout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller callerId CopyHelperUnit.layout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (immediateLocals : ∀ slot ∈ (LocalOperands.cachedLayoutFrame frame 0 CopyHelperUnit.layout valid0).locals,
      ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (finalMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory finalMemory)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let cached := LocalOperands.cachedLayoutFrame frame 0 CopyHelperUnit.layout valid0
    let popped := GenericPopFrame.afterRelevanceAt (frames.push caller) cached
      (ActualPopPlan.released (PtrMetadataReturn.accountedMachine options remaining span machine) finalMemory tracker borrowFrame)
      (thread.topUserRelevantFrame.getD (frames.push caller).size)
    ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) frame machine) =
      (Storage.withCurrent frames
        {PtrMetadataExecution.writeFrame caller callerId .uninit callerValid with location := .mir ⟨target,0⟩}
        popped,.ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let before := Storage.withCurrent (frames.push caller) frame machine
  let next := PtrMetadataReturn.accountedMachine options remaining span machine
  let nextState := Storage.withCurrent (frames.push caller) frame next
  have nextGhost : next.user.payload.ghost = false := by rw [PtrMetadataReturn.accounted_ghost];exact ghost
  have nextShallow : next.user.payload.validation = .Shallow := by rw [PtrMetadataReturn.accounted_validation];exact shallow
  have returned := return_driver options limits remaining span debugOff fuel validationFuel frames caller frame next
    sourceBody identity callee location valid0 live0 uncached0 noClocks callerId callerValid callerOld
    callerLive callerCached callerClocks destination target unwindAction continuation immediateLocals varargs
    tracker borrowFrame tracked frameTracked finalMemory plan thread active nextGhost nextShallow
  have accounting := SourceControl.before_terminator config limits () before
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks config limits).beforeTerminator () before = (nextState,.ok ()) := accounting
  let block := HelperCompilerFacts.copyBody.body.basicBlocks[7]'(by decide +kernel)
  have blockAt : frame.body.basicBlocks[7]? = some block := by rw [sourceBody];simp [block]
  have noStatement : block.statements[12]? = none := by decide +kernel
  have kind : block.terminator.kind = .Return := by decide +kernel
  exact GenericCallReturn.return_step_exact config limits () before nextState _ frame ⟨7,12⟩ block
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) location blockAt noStatement kind accounting' returned

#print axioms return_driver
open Lean Elab Command in
run_cmd do
  for declaration in [``return_driver, ``return_step] do
   for dependency in (← collectAxioms declaration) do
     unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
       throwError "unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperReturnDriver
