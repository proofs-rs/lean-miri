import duplicate_prefix.LenReleaseShape
namespace DuplicatePrefix.LenReleaseReturn
noncomputable section
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory Miri.TreeBorrows Miri.Concurrency
open PtrMetadataExecution PtrMetadataReturn
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem driver
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
    (shape : LenReleaseShape.Shape tracker.global.protectedTags borrowFrame.protectedTags machine.memory)
    (thread : ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ControlFlow.returnFromCurrentFrame (GenericCallReturn.sourceControl config limits) () false
      (Storage.withCurrent (frames.push caller) frame machine) =
      (Storage.withCurrent frames
        {writeFrame caller callerLocal (.scalar (.fromScalarInt (.ofUInt64 len))) callerValid0 with location := .mir ⟨target,0⟩}
        (poppedMachine frames caller frame (ActualPopPlan.released machine (LenReleaseShape.resultMemory shape) tracker borrowFrame) (thread.topUserRelevantFrame.getD (frames.push caller).size)),.ok ()) := by
  exact LenReturn.driver_with_plan options limits remaining span debugOff fuel validationFuel frames caller frame machine len sourceBody location valid0 live0 cached0 noClocks callerLocal callerValid0 callerLive0 callerCached0 callerClocks destination target unwindAction continuation immediateLocals varargs tracker borrowFrame tracked frameTracked (LenReleaseShape.resultMemory shape) (LenReleaseShape.plan shape) thread active ghost shallow

theorem step
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
    (shape : LenReleaseShape.Shape tracker.global.protectedTags borrowFrame.protectedTags machine.memory)
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
        (poppedMachine frames caller frame (ActualPopPlan.released (accountedMachine options remaining span machine) (LenReleaseShape.resultMemory shape) tracker borrowFrame) (thread.topUserRelevantFrame.getD (frames.push caller).size)),.ok true) := by
  exact LenReturn.step_with_plan options limits remaining span debugOff fuel validationFuel frames caller frame machine len sourceBody location valid0 live0 cached0 noClocks callerLocal callerValid0 callerLive0 callerCached0 callerClocks destination target unwindAction continuation immediateLocals varargs tracker borrowFrame tracked frameTracked (LenReleaseShape.resultMemory shape) (LenReleaseShape.plan shape) thread active unchecked noGc fixed ghost shallow

end
end DuplicatePrefix.LenReleaseReturn
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.LenReleaseReturn.driver, ``DuplicatePrefix.LenReleaseReturn.step] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved structural len Return {dependency}"
