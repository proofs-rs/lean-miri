import duplicate_prefix.CopyRootEntry
import duplicate_prefix.CopyHelperEntryBody
import duplicate_prefix.LanguageZeroStep
import duplicate_prefix.LanguageZeroInstalled
namespace DuplicatePrefix.CopyRootGuardEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
variable (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
  (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
  (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
  (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
  (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64)
  (input : CopyRootEntry.Input options limits remaining span frames caller machine sourcePointer destinationPointer n)
noncomputable def copyFrame := CopyRootEntry.enteredFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input
noncomputable def rootFrame := CopyRootEntry.cachedCaller options limits remaining span frames caller machine sourcePointer destinationPointer n input
noncomputable def copyMachine := CopyPushPreserves.post options remaining span machine
 theorem copy_size : (copyFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input).locals.size = 17 := by
  unfold copyFrame CopyRootEntry.enteredFrame
  rw [CopyEntryShape.locals]
  rfl
noncomputable def prepared :=
  let original := copyFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let first := SourceSteps.liveFrame original ⟨0,0⟩ 4 (by rw [copy_size];decide)
  SourceSteps.liveFrame first ⟨0,1⟩ 5 (by simp [first,SourceSteps.liveFrame,original,copy_size])
 theorem prepared_size : (prepared options limits remaining span frames caller machine sourcePointer destinationPointer n input).locals.size = 17 := by
  simp [prepared,SourceSteps.liveFrame,copy_size]
noncomputable def languageState := Storage.withCurrent
  (frames.push (rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input))
  (LanguageZeroUncached.cachedCaller (prepared options limits remaining span frames caller machine sourcePointer destinationPointer n input) (by rw [prepared_size];decide))
  (LanguageZeroStep.accountedMachine options remaining span (copyMachine options remaining span machine))
noncomputable def languageDestination := LanguageZeroEntry.destination
  (frames.push (rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input))
  (prepared options limits remaining span frames caller machine sourcePointer destinationPointer n input)
noncomputable def entered := Storage.withCurrent
  ((frames.push (rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input)).push
    (LanguageZeroUncached.cachedCaller (prepared options limits remaining span frames caller machine sourcePointer destinationPointer n input) (by rw [prepared_size];decide)))
  (LanguageZeroInstalled.frame options (languageState options limits remaining span frames caller machine sourcePointer destinationPointer n input)
    (languageDestination options limits remaining span frames caller machine sourcePointer destinationPointer n input))
  (LanguageZeroEntry.pushedMachine options (languageState options limits remaining span frames caller machine sourcePointer destinationPointer n input)
    (languageDestination options limits remaining span frames caller machine sourcePointer destinationPointer n input)
    (rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input))
 theorem from_copy : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
    (CopyRootEntry.entered options limits remaining span frames caller machine sourcePointer destinationPointer n input)
    (entered options limits remaining span frames caller machine sourcePointer destinationPointer n input) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let root := rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let frame := copyFrame options limits remaining span frames caller machine sourcePointer destinationPointer n input
  let next := copyMachine options remaining span machine
  let before := frames.push root
  have locals := CopyEntryShape.locals
    (Storage.withCurrent frames root (CopyCallStep.accountedMachine options remaining span machine))
    (LocalPlaces.localRuntimePlace frames.size root 18 CopyHelperUnit.layout).stackView
    (.goto (some 9) .Continue) input.noRace sourcePointer destinationPointer n
  change frame.locals = _ at locals
  have size : frame.locals.size = 17 := copy_size _ _ _ _ _ _ _ _ _ _ input
  have v4 : (4 : MIR.LocalId) < frame.locals.size := by rw [size];decide
  have v5 : (5 : MIR.LocalId) < frame.locals.size := by rw [size];decide
  have clocks : frame.extra.dataRace = none := CopyEntryShape.no_clocks _ _ _ input.noRace _ _ _
  let first := SourceSteps.liveFrame frame ⟨0,0⟩ 4 v4
  have firstStep := CopyHelperSteps.storage_live options limits (remaining+1) span before frame next ⟨0,0⟩ 4 2
    rfl rfl (by decide +kernel) (by decide +kernel) RootCompilerFacts.root_storage_trivial_type2 v4
    (by simp [locals]) clocks
  have v5First : (5 : MIR.LocalId) < first.locals.size := by simpa [first,SourceSteps.liveFrame] using v5
  let ready := prepared options limits remaining span frames caller machine sourcePointer destinationPointer n input
  have secondStep := CopyHelperSteps.storage_live options limits (remaining+1) span before first next ⟨0,1⟩ 5 0
    rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) v5First
    (by simp [first,SourceSteps.liveFrame,Array.getElem_set,locals]) clocks
  have readySize : 5 < ready.locals.size := by change 5 < (prepared _ _ _ _ _ _ _ _ _ _ input).locals.size;rw [prepared_size];decide
  have readyLive : ready.locals[5].value = .live (.immediate .uninit) := by
    simp [ready,prepared,SourceSteps.liveFrame,Array.getElem_set]
  have readyUncached : ready.locals[5].layout = none := by
    simp [ready,prepared,SourceSteps.liveFrame,Array.getElem_set,locals,frame,copyFrame,CopyRootEntry.enteredFrame,CopyEntryShape.locals]
  have nextActive : next.threads.activeThread? = some input.thread := by
    change (CopyPushPreserves.post options remaining span machine).threads.activeThread? = _
    rw [(CopyPushPreserves.fields options remaining span machine).2.2.1]
    exact input.active
  have top : FrameRelevance.top
      (LanguageZeroEntryFacts.pushed options.userRelevantCrates
        (Storage.withCurrent before (LanguageZeroUncached.cachedCaller ready readySize)
          (LanguageZeroStep.accountedMachine options remaining span next))
        (LanguageZeroEntry.destination before ready)).stack input.thread.topUserRelevantFrame = some frames.size := by
    simp [FrameRelevance.top,input.top]
  have present : (LanguageZeroEntryFacts.pushed options.userRelevantCrates
      (Storage.withCurrent before (LanguageZeroUncached.cachedCaller ready readySize)
        (LanguageZeroStep.accountedMachine options remaining span next))
      (LanguageZeroEntry.destination before ready)).stack.frames[frames.size]? = some root := by
    dsimp only [LanguageZeroEntryFacts.pushed,Storage.withCurrent,before]
    rw [Array.getElem?_push_lt (by simp only [Array.size_push]; omega)]
    simp [Array.getElem_push]
  have nextUnchecked : (config.terminators.getControl next.user).checkedArithmetic = false := by
    dsimp only [config,next,copyMachine]
    rw [CopyPushPreserves.control]
    exact input.unchecked
  have nextGc : (config.terminators.getControl next.user).gcInterval = 0 := by
    dsimp only [config,next,copyMachine]
    rw [CopyPushPreserves.control]
    exact input.noGc
  have fields := CopyPushPreserves.fields options remaining span machine
  have call := LanguageZeroStep.step options limits remaining input.budget input.budgetEq span input.source input.cmp input.debug
    before ready next rfl rfl rfl rfl readySize readyLive readyUncached clocks
    (fields.2.2.2.1.trans input.noRace) (fields.2.2.2.2.2.2.2.1.trans input.backend)
    (fields.2.2.2.2.2.1.trans input.ghost) input.tracker (fields.2.1.trans input.tracked)
    input.thread frames.size root nextActive top present nextUnchecked nextGc
    (by change (CopyPushPreserves.post options remaining span machine).threads.fixedScheduling = true; rw [fields.2.2.1];exact input.fixed)
  exact .next firstStep (.next secondStep (.next call (.refl _)))
 theorem run : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
    (Storage.withCurrent frames caller machine)
    (entered options limits remaining span frames caller machine sourcePointer destinationPointer n input) :=
  SuccessfulTrace.append
    (CopyRootEntry.trace options limits remaining span frames caller machine sourcePointer destinationPointer n input)
    (from_copy options limits remaining span frames caller machine sourcePointer destinationPointer n input)
#print axioms from_copy
#print axioms run
end DuplicatePrefix.CopyRootGuardEntry
