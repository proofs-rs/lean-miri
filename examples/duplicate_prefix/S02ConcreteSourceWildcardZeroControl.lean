import duplicate_prefix.S02ConcreteSourceWildcardInstalledBoth
import duplicate_prefix.AsMutPushPreserves
import duplicate_prefix.RootZeroInvocationState

namespace DuplicatePrefix.S02ConcreteSourceWildcardZeroControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Control and resource facts needed by the actual count-zero body/Return. -/
structure Settings (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (destinationId : AllocId)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) where
  tracker : MachineHooks.BorrowState
  enabled : machine.borrowTracker = some tracker
  mode : tracker.retagMode = .Default
  thread : Miri.Concurrency.ThreadRecord
  active : machine.threads.activeThread? = some thread
  race : machine.dataRace = none
  backend : machine.user.payload.payload.user.backend = .none
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0
  fixed : machine.threads.fixedScheduling = true
  extras : machine.user.payload.payload.user.runtime.extras.allocations.find?
    (fun row => row.1 == destinationId) = some (destinationId,⟨none,#[]⟩)
  fuel : Nat
  validationFuel : options.limits.validation = fuel+1
  debugOff : options.place.debugAssertions = false

/-- Contract-derived settings at the exact positive concrete argument and
wildcard destination protector state. No body or Return outcome is assumed. -/
theorem at_protection
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
    (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (destination : DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker firstFresh reference.id reference.entry tag reference.offset len) place)
    (destinationId : destination.id = input.contract.destination.id)
    (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree) :
    let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
      reference.tracker firstFresh reference.id reference.entry tag reference.offset len
    let root := RawRootInvocation.root before place input.contract.model.noDataRace
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
        (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
    let frame := (RootArgumentsTwo.result
      (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
        reference.id reference.tracker.global.nextPointerTag) 0).frame
    let changed := {frame with location := .unwinding ⟨601⟩}
    let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
    let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
    Nonempty (Settings options remaining span destination.id after.machine) := by
  let rawMachine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawFnEntryScope.resultMachine rawMachine reference.tracker firstFresh
    reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) 0).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let tracker := TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  have enabled : after.machine.borrowTracker = some tracker := rfl
  obtain ⟨originalTracker,originalEnabled,originalMode⟩ := input.contract.model.defaultTracker
  have referenceMode : reference.tracker.retagMode = .Default := by
    have same : reference.tracker = originalTracker :=
      Option.some.inj (reference.enabled.symm.trans originalEnabled)
    rw [same]
    exact originalMode
  have destinationMode : destination.tracker.retagMode = .Default := by
    have same : destination.tracker =
        ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
          reference.tracker.retagMode⟩ :=
      Option.some.inj (destination.enabled.symm.trans (show current.borrowTracker =
        some ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
          reference.tracker.retagMode⟩ from rfl))
    rw [same]
    exact referenceMode
  have mode : tracker.retagMode = .Default := by
    simpa only [tracker,TypedBorrowSteps.registeredTracker,ReferenceBorrowDriver.allocatedTracker]
      using destinationMode
  obtain ⟨_,_,raceEq,_addressesEq,ghostEq,shallowEq,_typesEq,backendEq,_⟩ :=
    RawRootInvocation.preservation #[] before
  have user : after.machine.user = rawMachine.user := rfl
  have threads : after.machine.threads = rawMachine.threads := rfl
  have raceEq' : after.machine.dataRace = rawMachine.dataRace := rfl
  have rawActive : rawMachine.threads.activeThread? =
      some {input.contract.thread with topUserRelevantFrame := some 0} := by
    change (CallEntryFacts.cacheTop (CallEntryFacts.freshRoot before).1 0).threads.activeThread? = _
    exact AsMutPushPreserves.active_cache (CallEntryFacts.freshRoot before).1 input.contract.thread
      (by simpa only [CallEntryFacts.freshRoot] using input.contract.active) 0
  have fuelPositive : 0 < options.limits.validation := by
    have bound := input.contract.resources.configuredFuel.2.2.2
    unfold DuplicatePrefixCallSpecification.work at bound
    omega
  let fuel := options.limits.validation - 1
  have validationFuel : options.limits.validation = fuel+1 := by
    dsimp only [fuel]
    omega
  have extras : after.machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,#[]⟩) := by
    rw [user,(RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2,destinationId]
    exact input.return_extras
  exact ⟨{
    tracker := tracker
    enabled := enabled
    mode := mode
    thread := {input.contract.thread with topUserRelevantFrame := some 0}
    active := by rw [threads]; exact rawActive
    race := by rw [raceEq',raceEq]; exact input.contract.model.noDataRace
    backend := by rw [user,backendEq]; exact input.contract.model.noBackend
    ghost := by rw [user,ghostEq]; exact input.contract.model.ghostOff
    shallow := by rw [user,shallowEq]; exact input.contract.model.shallow
    unchecked := by
      rw [user]
      change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
        rawMachine.user).checkedArithmetic = false
      rw [RootZeroInvocationState.raw_control]
      exact input.contract.model.unchecked
    noGc := by
      rw [user]
      change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
        rawMachine.user).gcInterval = 0
      rw [RootZeroInvocationState.raw_control]
      exact input.contract.model.noGc
    fixed := by
      rw [threads]
      change before.threads.fixedScheduling = true
      exact input.contract.model.fixedScheduler
    extras := extras
    fuel := fuel
    validationFuel := validationFuel
    debugOff := input.contract.model.debugOff }⟩

end
end DuplicatePrefix.S02ConcreteSourceWildcardZeroControl

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02ConcreteSourceWildcardZeroControl.at_protection) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved concrete-source wildcard zero-control dependency {dependency}"
