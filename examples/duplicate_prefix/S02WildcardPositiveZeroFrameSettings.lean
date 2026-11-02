import duplicate_prefix.S02WildcardSeparateConcreteJoined
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.AsMutPushPreserves

namespace DuplicatePrefix.S02WildcardPositiveZeroFrameSettings
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Internal exact-protection adapter. Public callers derive its operation premises
from the original contract, so independently assembled packets can reuse their
own wildcard witness. -/
theorem ready_from_protect
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len)
    (output : GeneralBorrowForestFnEntry.Output)
    (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
    (argument :
      let machine := RawRootInvocation.machine #[] before
      let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine machine reference.tracker firstFresh
        reference.id reference.entry output.child.tree
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks
          (PreparedContracts.actualConfig options () (remaining+1) span) limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len)
          (EmptyRootArguments.second 0))
        (Storage.withCurrent #[] root.frame machine) =
        .ok (2,2) (Storage.withCurrent #[]
          (RootArgumentsTwo.result
            (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
              reference.id reference.tracker.global.nextPointerTag) 0).frame current))
    (destination : DuplicatePrefixReturnPlaceInput.Input
      (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
        (RawRootInvocation.machine #[] before) reference.tracker firstFresh
        reference.id reference.entry output.child.tree) place)
    (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (protect :
      let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
        (RawRootInvocation.machine #[] before) reference.tracker firstFresh
        reference.id reference.entry output.child.tree
      let root := RawRootInvocation.root before place input.contract.model.noDataRace
      let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
      let frame := (RootArgumentsTwo.result
        (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
          reference.id reference.tracker.global.nextPointerTag) 0).frame
      let changed := {frame with location := .unwinding ⟨601⟩}
      let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
      let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
      TypedRetag.protectInPlaceFunctionArgument (config options (remaining+1) span).retag
        limits.retag place (Storage.withCurrent #[] changed current) = .ok () after) :
      ∃ (frame : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
      (thread : Miri.Concurrency.ThreadRecord)
      (fuel : Nat),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second 0)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
      frame.body = RootBody.reflected.body.body ∧
      frame.bodyIdentity = RootBody.reflected.body.identity ∧
      frame.functionInstance = RootBody.reflected.functionInstance ∧
      frame.location = .mir ⟨0,0⟩ ∧ frame.locals.size = 25 ∧
      frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩ ∧
      frame.locals[3]? = some ⟨.dead,none⟩ ∧
      frame.locals[4]? = some ⟨.dead,none⟩ ∧
      frame.locals[5]? = some ⟨.dead,none⟩ ∧
      frame.extra.dataRace = none ∧ frame.extra.borrowTracker = some borrowFrame ∧
      frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ ∧
      frame.returnContinuation = .stop true ∧ CopyHelperCleanup.AllImmediate frame ∧
      frame.vaList = #[] ∧
      machine.borrowTracker = some tracker ∧ tracker.retagMode = .Default ∧
      machine.threads.activeThread? = some thread ∧ machine.dataRace = none ∧
      machine.user.payload.payload.user.backend = .none ∧
      machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 ∧
      machine.threads.fixedScheduling = true ∧
      machine.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras ∧
      machine.user.payload.payload.user.runtime.extras.allocations.find?
        (fun row => row.1 == input.contract.destination.id) =
          some (input.contract.destination.id,⟨none,#[]⟩) ∧
      options.place.debugAssertions = false ∧ options.limits.validation = fuel+1 := by
  let rawMachine := RawRootInvocation.machine #[] before
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine rawMachine reference.tracker firstFresh
    reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let args := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) 0).frame
  let changed := {args with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let frame := PositiveRootInstalledFrame.installed root adjusted 0 {}
    reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag
  have actual := S02WildcardFinishFromProtect.init address len 0 input nonempty
    reference output firstFresh argument destination secondFresh tree updated protect
  have metadata := PositiveRootInstalledFrame.metadata root adjusted 0 {}
    reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag
  have slots := PositiveRootInstalledFrame.slot_option root
    (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted 0 {}
    reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag
  have immediate := PositiveRootInstalledFrame.immediate root
    (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted 0 {}
    reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag
  have size := PositiveRootInstalledFrame.size root adjusted 0 {}
    reference.id reference.tracker.global.nextPointerTag destination.id destination.tracker.global.nextPointerTag
  let tracker := TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  have tracked : after.machine.borrowTracker = some tracker := rfl
  obtain ⟨originalTracker,originalEnabled,originalMode⟩ := input.contract.model.defaultTracker
  have refMode : reference.tracker.retagMode = .Default := by
    have same : reference.tracker = originalTracker :=
      Option.some.inj (reference.enabled.symm.trans originalEnabled)
    rw [same]
    exact originalMode
  have destMode : destination.tracker.retagMode = .Default := by
    have same : destination.tracker =
        ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh, reference.tracker.retagMode⟩ := by
      exact Option.some.inj (destination.enabled.symm.trans (show current.borrowTracker =
        some ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh, reference.tracker.retagMode⟩ from rfl))
    rw [same]
    exact refMode
  have nextMode : tracker.retagMode = .Default := by
    simpa only [tracker,TypedBorrowSteps.registeredTracker,ReferenceBorrowDriver.allocatedTracker] using destMode
  obtain ⟨_,_,raceEq,_addressesEq,ghostEq,shallowEq,_typesEq,backendEq,_⟩ := RawRootInvocation.preservation #[] before
  have postUser : after.machine.user = rawMachine.user := rfl
  have postThreads : after.machine.threads = rawMachine.threads := rfl
  have postRace : after.machine.dataRace = rawMachine.dataRace := rfl
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
  have extras : after.machine.user.payload.payload.user.runtime.extras =
      before.user.payload.payload.user.runtime.extras := by
    change rawMachine.user.payload.payload.user.runtime.extras = _
    exact (RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2
  have returnExtras : after.machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == input.contract.destination.id) =
        some (input.contract.destination.id,⟨none,#[]⟩) := by
    rw [extras]
    exact input.return_extras
  let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
  refine ⟨frame,after.machine,tracker,borrowFrame,
    {input.contract.thread with topUserRelevantFrame := some 0},fuel,actual,
    ?_,?_,?_,metadata.2.2.2.2.2.2.2.2,size,?_,?_,?_,?_,?_,?_,
    metadata.2.2.2.2.2.2.2.1,?_,?_,immediate,?_,tracked,nextMode,?_,?_,?_,?_,?_,?_,?_,?_,extras,returnExtras,?_,validationFuel⟩
  · exact metadata.1
  · exact metadata.2.1
  · exact metadata.2.2.1
  · simpa using slots ⟨0,by decide⟩
  · simpa using slots ⟨2,by decide⟩
  · simpa using slots ⟨3,by decide⟩
  · simpa using slots ⟨4,by decide⟩
  · simpa using slots ⟨5,by decide⟩
  · exact metadata.2.2.2.2.2.2.1.trans root.noClocks
  · rw [metadata.2.2.2.2.1]; rfl
  · exact metadata.2.2.2.1
  · rw [metadata.2.2.2.2.2.1]; rfl
  · rw [postThreads]; exact rawActive
  · rw [postRace,raceEq]; exact input.contract.model.noDataRace
  · rw [postUser,backendEq]; exact input.contract.model.noBackend
  · rw [postUser,ghostEq]; exact input.contract.model.ghostOff
  · rw [postUser,shallowEq]; exact input.contract.model.shallow
  · rw [postUser]
    change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).checkedArithmetic = false
    rw [RootZeroInvocationState.raw_control]
    exact input.contract.model.unchecked
  · rw [postUser]
    change ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).gcInterval = 0
    rw [RootZeroInvocationState.raw_control]
    exact input.contract.model.noGc
  · rw [postThreads]
    change before.threads.fixedScheduling = true
    exact input.contract.model.fixedScheduler
  · exact input.contract.model.debugOff


/-- Count-zero frame and control settings at the actual wildcard call result,
derived from the original contract and allocation classification. -/
theorem ready
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
      ∃ (frame : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
      (thread : Miri.Concurrency.ThreadRecord)
      (fuel : Nat),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second 0)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
      frame.body = RootBody.reflected.body.body ∧
      frame.bodyIdentity = RootBody.reflected.body.identity ∧
      frame.functionInstance = RootBody.reflected.functionInstance ∧
      frame.location = .mir ⟨0,0⟩ ∧ frame.locals.size = 25 ∧
      frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩ ∧
      frame.locals[3]? = some ⟨.dead,none⟩ ∧
      frame.locals[4]? = some ⟨.dead,none⟩ ∧
      frame.locals[5]? = some ⟨.dead,none⟩ ∧
      frame.extra.dataRace = none ∧ frame.extra.borrowTracker = some borrowFrame ∧
      frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ ∧
      frame.returnContinuation = .stop true ∧ CopyHelperCleanup.AllImmediate frame ∧
      frame.vaList = #[] ∧
      machine.borrowTracker = some tracker ∧ tracker.retagMode = .Default ∧
      machine.threads.activeThread? = some thread ∧ machine.dataRace = none ∧
      machine.user.payload.payload.user.backend = .none ∧
      machine.user.payload.ghost = false ∧ machine.user.payload.validation = .Shallow ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 ∧
      machine.threads.fixedScheduling = true ∧
      machine.user.payload.payload.user.runtime.extras = before.user.payload.payload.user.runtime.extras ∧
      machine.user.payload.payload.user.runtime.extras.allocations.find?
        (fun row => row.1 == input.contract.destination.id) =
          some (input.contract.destination.id,⟨none,#[]⟩) ∧
      options.place.debugAssertions = false ∧ options.limits.validation = fuel+1 := by
  obtain ⟨reference,output,firstFresh,argument,ready⟩ :=
    S02WildcardSeparateConcreteProtectSource.source_after_protect address len 0 input nonempty
      returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨destination,secondFresh,tree,updated,sourceChild,sourceNode,sourceTracker,
    protect,_tracked,_sourceLive,_sourceTagged,_sourcePresent,_sourceTag,_parentless,_leaf,_hidden,
    _sourceRuntime,_sourcePositive,_sourceActivity,_sourceDistinct,_sourceOrder,_sourceShort⟩ := ready different
  exact ready_from_protect address len input nonempty reference output firstFresh argument
    destination secondFresh tree updated protect

end
end DuplicatePrefix.S02WildcardPositiveZeroFrameSettings

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02WildcardPositiveZeroFrameSettings.ready,
      ``DuplicatePrefix.S02WildcardPositiveZeroFrameSettings.ready_from_protect] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved wildcard zero frame/settings dependency {dependency}"
