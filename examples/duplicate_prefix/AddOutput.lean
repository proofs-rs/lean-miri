import duplicate_prefix.AddRootComplete
namespace DuplicatePrefix.AddOutput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
noncomputable def caller (frame : CompilerFrameContext.ActualFrame) (valid : 21 < frame.locals.size)
    (value : Scalar Provenance) :=
  let cached := AddUncachedCall.cachedCaller frame valid
  {PointerAddReturn.writeFrame cached 21 (.scalar value) (by simpa [cached,AddUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using valid)
    with location := .mir ⟨8,0⟩}
 theorem slot21 (frame : CompilerFrameContext.ActualFrame) (valid : 21 < frame.locals.size) (value : Scalar Provenance) :
    (caller frame valid value).locals[21]'(by simpa [caller,PointerAddReturn.writeFrame,AddUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout] using valid) =
      ⟨.live (.immediate (.scalar value)),some CopyCompilerFacts.destPointerLayout⟩ := by
  simp only [caller,PointerAddReturn.writeFrame,AddUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
 theorem metadata (frame : CompilerFrameContext.ActualFrame) (valid : 21 < frame.locals.size) (value : Scalar Provenance) :
    (caller frame valid value).body = frame.body ∧
    (caller frame valid value).bodyIdentity = frame.bodyIdentity ∧
    (caller frame valid value).functionInstance = frame.functionInstance ∧
    (caller frame valid value).extra = frame.extra ∧
    (caller frame valid value).returnContinuation = frame.returnContinuation ∧
    (caller frame valid value).returnPlace = frame.returnPlace ∧
    (caller frame valid value).vaList = frame.vaList ∧
    (caller frame valid value).localsIdentity = frame.localsIdentity ∧
    (caller frame valid value).locals.size = frame.locals.size ∧
    (caller frame valid value).location = .mir ⟨8,0⟩ := by
  simp only [caller,PointerAddReturn.writeFrame,AddUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set]
  repeat' constructor
 theorem other (frame : CompilerFrameContext.ActualFrame) (valid : 21 < frame.locals.size)
    (value : Scalar Provenance) (index : Nat) (different : index ≠ 21) :
    (caller frame valid value).locals[index]? = frame.locals[index]? := by
  simp only [caller,PointerAddReturn.writeFrame,AddUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,
    Array.getElem?_set,different,Ne.symm different,ite_false]
 theorem tracked_caller (frame : CompilerFrameContext.ActualFrame) (valid : 21 < frame.locals.size) (value : Scalar Provenance) :
    (caller frame valid value).trackCallerArg = frame.trackCallerArg := by
  simp only [caller,PointerAddReturn.writeFrame,AddUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout]
 theorem all_immediate (frame : CompilerFrameContext.ActualFrame) (valid : 21 < frame.locals.size) (value : Scalar Provenance)
    (direct : ∀ current ∈ frame.locals, ∀ memory, current.value ≠ .live (.indirect memory)) :
    ∀ current ∈ (caller frame valid value).locals, ∀ memory, current.value ≠ .live (.indirect memory) := by
  intro current member memory
  obtain ⟨index,bounded,eqCurrent⟩ := Array.mem_iff_getElem.mp member
  by_cases same : index = 21
  · subst index
    rw [← eqCurrent,slot21]
    simp
  · have outSome : (caller frame valid value).locals[index]? = some current := by
      rw [Array.getElem?_eq_getElem bounded,eqCurrent]
    rw [other frame valid value index same] at outSome
    exact direct current (Array.mem_of_getElem? outSome) memory
noncomputable def machine (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :=
  PointerAddReturn.accountedMachine options remaining span (AddPushPreserves.post options remaining span before)
 theorem preserved (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    (machine options remaining span before).memory = before.memory ∧
    (machine options remaining span before).borrowTracker = before.borrowTracker ∧
    (machine options remaining span before).threads = before.threads ∧
    (machine options remaining span before).dataRace = before.dataRace ∧
    (machine options remaining span before).user.addresses = before.user.addresses ∧
    (machine options remaining span before).user.payload.ghost = before.user.payload.ghost ∧
    (machine options remaining span before).user.payload.validation = before.user.payload.validation ∧
    (machine options remaining span before).user.payload.payload.user.backend = before.user.payload.payload.user.backend ∧
    (machine options remaining span before).user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras ∧
    (machine options remaining span before).user.payload.payload.user.types = before.user.payload.payload.user.types := by
  unfold machine PointerAddReturn.accountedMachine AddPushPreserves.post CallEntryFacts.freshRoot
    AddCallStep.accountedMachine PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  repeat' constructor
 theorem control (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl (machine options remaining span before).user =
      TerminatorClock.advance (TerminatorClock.advance ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user)) := by
  unfold machine PointerAddReturn.accountedMachine AddPushPreserves.post CallEntryFacts.freshRoot
    AddCallStep.accountedMachine PtrMetadataReturn.accountedMachine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl
end DuplicatePrefix.AddOutput
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.AddOutput." then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved add output dependency {dependency}"
