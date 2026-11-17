import duplicate_prefix.ParentFalseAssignment
import duplicate_prefix.ParentFalseTail
import duplicate_prefix.ParentFalseReturn
import duplicate_prefix.CanonicalConfigFacts

/-! Actual assignment, branch goto, StorageDead and Return on the false branch
of the pinned language guard. -/
namespace DuplicatePrefix.ParentFalseBranchTail
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open DuplicatePrefix
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem run [DecidableEq MiriMemoryKind] [PointerProvenance Provenance]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining fuel : Nat) (span : PreparedContracts.FixedSpanQuery)
    (source : PreparedContracts.SourceComparator)
    (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (framesEq : frames = framesBefore.push caller)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : frame.location = .mir ⟨3,0⟩)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (uninit0 : frame.locals[0].value = .live (.immediate .uninit))
    (uncached0 : frame.locals[0].layout = none)
    (valid1 : (1 : MIR.LocalId) < frame.locals.size)
    (live1 : frame.locals[1].value = .live (.immediate (.scalar (.fromBool false))))
    (cached1 : frame.locals[1].layout = some RootCompilerFacts.boolLayout)
    (valid1Assigned : (1 : MIR.LocalId) <
      (ParentFalseAssignment.falseReturnFrame frame valid0).locals.size)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (callerValid5 : (5 : MIR.LocalId) < caller.locals.size)
    (callerUninit5 : caller.locals[5].value = .live (.immediate .uninit))
    (callerCached5 : caller.locals[5].layout = some RootCompilerFacts.boolLayout)
    (callerNoClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace =
      LocalPlaces.localRuntimePlace framesBefore.size caller 5 RootCompilerFacts.boolLayout)
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind)
    (immediateLocals : ∀ slot ∈ (SourceSteps.deadFrame
      {ParentFalseAssignment.falseReturnFrame frame valid0 with location := .mir ⟨4,0⟩}
      ⟨4,0⟩ 1 valid1Assigned).locals,
      ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (borrowFrame : Miri.TreeBorrows.FrameState)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : Miri.Concurrency.ThreadRecord)
    (active : machine.threads.activeThread? = some thread) :
    ∃ afterAssign afterGoto afterDead afterReturn,
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        (Storage.withCurrent frames frame machine) = (afterAssign,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        afterAssign = (afterGoto,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        afterGoto = (afterDead,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        afterDead = (afterReturn,.ok true) ∧
      afterReturn = Storage.withCurrent framesBefore
        (ParentFalseReturn.returnedCallerFrame caller callerValid5 target)
        (ParentFalseReturn.poppedMachine framesBefore caller
          (SourceSteps.deadFrame
            {ParentFalseAssignment.falseReturnFrame frame valid0 with location := .mir ⟨4,0⟩}
            ⟨4,0⟩ 1 valid1Assigned)
          (SourceControl.accounted (PreparedContracts.actualConfig options () (remaining+1) span).terminators
            (Storage.withCurrent (framesBefore.push caller)
              (SourceSteps.deadFrame
                {ParentFalseAssignment.falseReturnFrame frame valid0 with location := .mir ⟨4,0⟩}
                ⟨4,0⟩ 1 valid1Assigned)
              (SourceControl.accounted (PreparedContracts.actualConfig options () (remaining+1) span).terminators
                (Storage.withCurrent frames
                  {ParentFalseAssignment.falseReturnFrame frame valid0 with location := .mir ⟨4,0⟩}
                  machine)).machine)).machine
          (thread.topUserRelevantFrame.getD (framesBefore.push caller).size)) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let assigned := ParentFalseAssignment.falseReturnFrame frame valid0
  let afterAssignFrame := {assigned with location := .mir ⟨3,1⟩}
  let atGoto := {afterAssignFrame with location := .mir ⟨4,0⟩}
  have valid1AtGoto : (1 : MIR.LocalId) < atGoto.locals.size := by
    simpa [atGoto,afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout,Array.size_set] using valid1
  let dead := SourceSteps.deadFrame atGoto ⟨4,0⟩ 1 valid1AtGoto
  let accounted := SourceControl.accounted config.terminators (Storage.withCurrent frames afterAssignFrame machine)
  let afterGotoMachine := accounted.machine
  have stepAssign := ParentFalseAssignment.source_step options limits remaining span source debugOff fuel
    validationFuel frames frame machine body identity callee location valid0 uninit0 uncached0 noClocks
    tracker tracked defaultMode ghost shallow
  have stepGoto := ParentFalseAssignment.goto_parent_false options limits (remaining+1) span frames afterAssignFrame machine
    (by simpa [afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout] using body)
    (by simp [afterAssignFrame]) unchecked noGc fixed
  have stepDead := ParentFalseTail.storage_dead_one_step options limits remaining span frames atGoto afterGotoMachine
    (by simpa [atGoto,afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout] using body)
    (by simp [atGoto]) valid1AtGoto
    (by simpa [atGoto,afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout,Array.getElem_set] using live1)
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have getSet : ∀ control user, config.terminators.getControl (config.terminators.setControl control user) = control := by
    rw [fields.terminators]
    intro control user
    rfl
  have accountedControl : afterGotoMachine.user = config.terminators.setControl
      (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user := by
    change (SourceControl.accounted config.terminators
      (Storage.withCurrent frames afterAssignFrame machine)).machine.user = _
    rw [fields.terminators]
    rfl
  let gotoUser := config.terminators.setControl
    (TerminatorClock.advance (config.terminators.getControl machine.user)) machine.user
  have accountedMachineEq : afterGotoMachine = {machine with user := gotoUser} := by
    change (SourceControl.accounted config.terminators
      (Storage.withCurrent frames afterAssignFrame machine)).machine = _
    simp [SourceControl.accounted,Storage.withCurrent,fields.terminators,gotoUser]
  have unchecked' : (config.terminators.getControl afterGotoMachine.user).checkedArithmetic = false := by
    rw [accountedControl,getSet]
    simpa [TerminatorClock.advance] using unchecked
  have noGc' : (config.terminators.getControl afterGotoMachine.user).gcInterval = 0 := by
    rw [accountedControl,getSet]
    simpa [TerminatorClock.advance] using noGc
  have ghost' : afterGotoMachine.user.payload.ghost = false := by
    rw [accountedControl,fields.terminators]
    exact ghost
  have shallow' : afterGotoMachine.user.payload.validation = .Shallow := by
    rw [accountedControl,fields.terminators]
    exact shallow
  have tracked' : afterGotoMachine.borrowTracker = some tracker := by rw [accountedMachineEq]; exact tracked
  have active' : afterGotoMachine.threads.activeThread? = some thread := by rw [accountedMachineEq]; exact active
  have fixed' : afterGotoMachine.threads.fixedScheduling = true := by rw [accountedMachineEq]; exact fixed
  have deadBody : dead.body = CopyPreconditions.Bodies.checkLanguage.loaded.body := by
    simpa [dead,SourceSteps.deadFrame,atGoto,afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout] using body
  have deadIdentity : dead.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity := by
    simpa [dead,SourceSteps.deadFrame,atGoto,afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout] using identity
  have deadCallee : dead.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance := by
    simpa [dead,SourceSteps.deadFrame,atGoto,afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout] using callee
  have deadLocation : dead.location = .mir ⟨4,1⟩ := by simp [dead,SourceSteps.deadFrame]
  have deadValid0 : (0 : MIR.LocalId) < dead.locals.size := by
    simpa [dead,SourceSteps.deadFrame,atGoto,afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout,Array.size_set] using valid0
  have deadLive0 : dead.locals[0].value = .live (.immediate (.scalar (.fromBool false))) := by
    simp [dead,SourceSteps.deadFrame,atGoto,afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout,Array.getElem_set,valid0]
  have deadCached0 : dead.locals[0].layout = some RootCompilerFacts.boolLayout := by
    simp [dead,SourceSteps.deadFrame,atGoto,afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout,Array.getElem_set,valid0]
  have deadNoClocks : dead.extra.dataRace = none := by
    simpa [dead,SourceSteps.deadFrame,atGoto,afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout] using noClocks
  have deadTracked : afterGotoMachine.borrowTracker = some tracker := tracked'
  have deadFrameTracked : dead.extra.borrowTracker = some borrowFrame := by
    simpa [dead,SourceSteps.deadFrame,atGoto,afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout] using frameTracked
  have returned := ParentFalseReturn.return_step options limits remaining span debugOff fuel validationFuel
    framesBefore caller dead afterGotoMachine deadBody deadIdentity deadCallee deadLocation deadValid0 deadLive0 deadCached0
    deadNoClocks callerValid5 callerUninit5 callerCached5 callerNoClocks
    (by simpa [dead,SourceSteps.deadFrame,atGoto,afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout] using destination)
    target unwind
    (by simpa [dead,SourceSteps.deadFrame,atGoto,afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout] using continuation)
    immediateLocals
    (by simpa [dead,SourceSteps.deadFrame,atGoto,afterAssignFrame,assigned,ParentFalseAssignment.falseReturnFrame,
      ParentFalseAssignment.cacheReturnLayout,LocalPlaces.cachePlaceLayout] using varargs)
    tracker borrowFrame deadTracked deadFrameTracked empty thread active' unchecked' noGc' fixed' ghost' shallow'
  refine ⟨Storage.withCurrent frames afterAssignFrame machine,
    Storage.withCurrent frames atGoto afterGotoMachine,
    Storage.withCurrent frames dead afterGotoMachine,
    Storage.withCurrent framesBefore (ParentFalseReturn.returnedCallerFrame caller callerValid5 target)
      (ParentFalseReturn.poppedMachine framesBefore caller dead
        (SourceControl.accounted config.terminators
          (Storage.withCurrent (framesBefore.push caller) dead afterGotoMachine)).machine
        (thread.topUserRelevantFrame.getD (framesBefore.push caller).size)), ?_, ?_, ?_, ?_, ?_⟩
  · simpa [assigned,afterAssignFrame] using stepAssign
  · simpa [afterAssignFrame,atGoto,afterGotoMachine] using stepGoto
  · simpa [atGoto,dead,afterGotoMachine] using stepDead
  · simpa [dead,afterGotoMachine,framesEq] using returned
  · rfl

#print axioms run
end DuplicatePrefix.ParentFalseBranchTail

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.ParentFalseBranchTail.run) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError s!"unapproved parent false branch tail dependency {dependency}"
