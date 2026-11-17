import duplicate_prefix.PtrMetadataReturn
import duplicate_prefix.PtrMetadataIntegerBody
/-! Complete five-step execution of the actual metadata wrapper, for provenance-carrying and integer pointers. The result is copied into the actual caller local before the helper frame is cleaned up and removed. -/
namespace DuplicatePrefix.PtrMetadataComplete
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
open PtrMetadataHelper PtrMetadataExecution PtrMetadataReturn
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def rawImmediate (carrier : Pointer Provenance ⊕ UInt64) (target : TargetDataLayout) (len : UInt64) : Immediate Provenance :=
  match carrier with
  | .inl pointer => (RetagReferencePlace.sliceValue target pointer len rawLayout).imm
  | .inr address => (RetagReferencePlace.integerSliceValue address len rawLayout).imm

def isDirect : LocalValue Provenance → Bool
  | .dead | .live (.immediate _) => true
  | .live (.indirect _) => false

theorem all_direct_three (slots : Array (LocalState Provenance LocalLayout))
    (size : slots.size = 3)
    (zero : slots[0]?.map (fun slot => isDirect slot.value) = some true)
    (one : slots[1]?.map (fun slot => isDirect slot.value) = some true)
    (two : slots[2]?.map (fun slot => isDirect slot.value) = some true) :
    ∀ slot ∈ slots, ∀ memory, slot.value ≠ .live (.indirect memory) := by
  intro slot member memory bad
  rcases Array.mem_iff_getElem.mp member with ⟨index,valid,equal⟩
  have cases3 : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  have flag : isDirect slot.value = true := by
    rcases cases3 with rfl | rfl | rfl
    · simpa [Array.getElem?_eq_getElem valid,equal] using zero
    · simpa [Array.getElem?_eq_getElem valid,equal] using one
    · simpa [Array.getElem?_eq_getElem valid,equal] using two
  rw [bad] at flag
  cases flag

theorem four_statements
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (size : frame.locals.size = 3)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate
      (rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached1 : (frame.locals[1]'(by omega)).layout = some rawLayout)
    (dead2 : (frame.locals[2]'(by omega)).value = .dead)
    (uncached2 : (frame.locals[2]'(by omega)).layout = none)
    (sourceBody : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ first second third done : CompilerFrameContext.ActualFrame,
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore frame machine) =
        (Storage.withCurrent framesBefore first machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore first machine) =
        (Storage.withCurrent framesBefore second machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore second machine) =
        (Storage.withCurrent framesBefore third machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore third machine) =
        (Storage.withCurrent framesBefore done machine,.ok true) ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧
      done.functionInstance = frame.functionInstance ∧ done.extra = frame.extra ∧
      done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧
      done.locals[1]? = frame.locals[1]? ∧
      done.locals.size = 3 ∧ done.location = .mir ⟨0,4⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (done.locals[2]?.map (·.value)) = some .dead := by
  cases carrier with
  | inl pointer =>
    exact PtrMetadataBody.actual_four_statements options limits remaining span debugOff fuel validationFuel
      framesBefore frame machine pointer len size live0 uncached0 live1 cached1 dead2 uncached2
      sourceBody identity callee location noClocks tracker tracked defaultMode ghostFalse shallow
  | inr address =>
    exact PtrMetadataIntegerBody.actual_four_statements options limits remaining span debugOff fuel validationFuel
      framesBefore frame machine address len size live0 uncached0 live1 cached1 dead2 uncached2
      sourceBody identity callee location noClocks tracker tracked defaultMode ghostFalse shallow

theorem body_returns_len
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (size : frame.locals.size = 3)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate
      (rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached1 : (frame.locals[1]'(by omega)).layout = some rawLayout)
    (dead2 : (frame.locals[2]'(by omega)).value = .dead)
    (uncached2 : (frame.locals[2]'(by omega)).layout = none)
    (sourceBody : frame.body = PtrMetadataHelper.body.body)
    (identity : frame.bodyIdentity = PtrMetadataHelper.body.identity)
    (callee : frame.functionInstance = PtrMetadataHelper.resolved.callee)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (callerValid0 : (0 : Miri.MIR.LocalId) < caller.locals.size)
    (callerLive0 : caller.locals[0].value = .live (.immediate .uninit))
    (callerCached0 : caller.locals[0].layout = some RootCompilerFacts.usizeLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller 0 RootCompilerFacts.usizeLayout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker) (defaultMode : tracker.retagMode = .Default)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ first second third done : CompilerFrameContext.ActualFrame,
      ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) frame machine) =
        (Storage.withCurrent (frames.push caller) first machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) first machine) =
        (Storage.withCurrent (frames.push caller) second machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) second machine) =
        (Storage.withCurrent (frames.push caller) third machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) third machine) =
        (Storage.withCurrent (frames.push caller) done machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) done machine) =
        (Storage.withCurrent frames
          {writeFrame caller 0 (.scalar (.fromScalarInt (.ofUInt64 len))) callerValid0 with location := .mir ⟨target,0⟩}
          (poppedMachine frames caller done (accountedMachine options remaining span machine)
            (thread.topUserRelevantFrame.getD (frames.push caller).size)),.ok true) ∧
      done.extra = frame.extra := by
  obtain ⟨first,second,third,done,step1,step2,step3,step4,
    doneBody,doneIdentity,doneFn,doneExtra,doneReturn,doneCont,doneVa,doneLocalsIdentity,doneArg,
    doneSize,doneLocation,done0,done2⟩ := four_statements options limits remaining span debugOff fuel validationFuel
      (frames.push caller) frame machine carrier len size live0 uncached0 live1 cached1 dead2 uncached2
      sourceBody identity callee location noClocks tracker tracked defaultMode ghost shallow
  have doneValid0 : (0 : Miri.MIR.LocalId) < done.locals.size := by rw [doneSize];decide
  have sourceValid1 : (1 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  have slot0 : done.locals[0] = ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ := by
    simpa only [Array.getElem?_eq_getElem doneValid0,Option.some.injEq] using done0
  have immediateLocals := all_direct_three done.locals doneSize
    (by simp [done0,isDirect])
    (by rw [doneArg,Array.getElem?_eq_getElem sourceValid1];simp [live1,isDirect])
    (by simpa only [Option.map_map,Function.comp_def,Option.map_some,isDirect] using congrArg (Option.map isDirect) done2)
  have step5 := return_step options limits remaining span debugOff fuel validationFuel frames caller done machine len
    (by rw [doneBody];exact sourceBody) doneLocation doneValid0
    (by rw [slot0]) (by rw [slot0])
    (by rw [doneExtra];exact noClocks)
    callerValid0 callerLive0 callerCached0 callerClocks
    (by rw [doneReturn];exact destination) target unwindAction
    (by rw [doneCont];exact continuation) immediateLocals
    (by rw [doneVa];exact varargs) tracker borrowFrame tracked
    (by rw [doneExtra];exact frameTracked) empty thread active unchecked noGc fixed ghost shallow
  exact ⟨first,second,third,done,step1,step2,step3,step4,step5,doneExtra⟩

#print axioms body_returns_len

#print axioms all_direct_three
open Lean Elab Command in
run_cmd do
  for declaration in #[``four_statements, ``body_returns_len] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"

end
end DuplicatePrefix.PtrMetadataComplete
