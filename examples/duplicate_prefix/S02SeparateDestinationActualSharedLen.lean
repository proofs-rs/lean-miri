import duplicate_prefix.S02SeparateDestinationSharedFullSite
import duplicate_prefix.S02SeparateDestinationSharedSiteBounds
import duplicate_prefix.S02SeparateDestinationSharedSiteGeometry
import duplicate_prefix.GeneralBorrowRawSharedToLen

namespace DuplicatePrefix.S02SeparateDestinationActualSharedLen
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual positive rejected call reaches and executes shared Ref and slice::len. -/
theorem executes
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (rejected : count > len/2) :
    ∃ (entry frame result : CompilerFrameContext.ActualFrame)
      (machine post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry machine)
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span machine)) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span machine))
        (Storage.withCurrent #[] result post) ∧ result.location = .mir ⟨3,0⟩ := by
  obtain ⟨reference,tracker,sourceEntry,child,raw,entry,frame,machine,actual,prefixTrace,
    body,identity,callee,located,size,noClocks,sourceCell,lenCell,exprCell,_immediate,
    tracked,live,sourceEq,counter,rawTag,rawParent,rawOffset,rawLen,runtime,activity⟩ :=
    S02SeparateDestinationSharedFullSite.actual_shared_full_site id tag address len count input
      nonempty different returnTag returnConcrete rejected
  obtain ⟨positive,nonzero,signedFits,_bounds,capacity,shortRoom,nodeRoom,tagRoom⟩ :=
    S02SeparateDestinationSharedSiteBounds.at_actual_call id tag address len count input
      nonempty different returnTag returnConcrete reference tracker sourceEntry entry machine
      actual tracked live
  obtain ⟨addresses,types,backend,ghost,shallow,unchecked,noGc,fixed,race,
    thread,active,topZero⟩ :=
    S02SeparateDestinationSharedSiteGeometry.after_tick id tag address len count input
      nonempty different returnTag returnConcrete entry machine actual
  let current := RootZeroCompleteState.tick options remaining span machine
  obtain ⟨_mem,tickTracker,_race,_threads,_addresses,_types,_backend,_extras⟩ :=
    S02SeparateDestinationTickLedger.preserved options remaining span machine
  have enabled : current.borrowTracker = some tracker := by rw [tickTracker]; exact tracked
  have present : current.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) := by
    rw [_mem]; exact live
  have cached : current.user.addresses.baseAddr.find? (fun row => row.allocId == reference.id) = some ⟨reference.id,reference.base⟩ := by
    rw [addresses]; exact reference.cachedBase
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame current)).metadata = PreparedReflection.actual.runtime := by
    change current.user.payload.payload.user.types.metadata = _
    rw [types]; exact input.contract.model.metadata
  have notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame current)).entries.any (·.value.ty == 4) = false := by
    change current.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [types]; exact input.slice_not_constructed
  obtain ⟨_ref2,tracker2,entry2,machine2,actual2,tracked2,mode2,_ghost2,_shallow2,
    _unchecked2,_gc2,_fixed2,_race2⟩ :=
    S02SeparateDestinationMachineSettings.after_exact id tag address len count input nonempty
      different returnTag returnConcrete
  have same2 : Storage.withCurrent #[] entry2 machine2 = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (actual2.symm.trans actual)).2
  have machineEq : machine2 = machine := congrArg (fun s : RootState => s.machine) same2
  have mode : tracker.retagMode = .Default := by
    have trackerEq : tracker2 = tracker := Option.some.inj (by rw [machineEq] at tracked2; exact tracked2.symm.trans tracked)
    rw [←trackerEq]
    exact mode2
  have fresh : tracker.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have h : tracker.global.nextPointerTag.value.toNat < 18446744073709551615 := by omega
    simpa using h
  have dynamicPositive : 0 < options.place.dynamicFuel := by
    have h := input.contract.resources.dynamicFuel
    unfold work at h
    omega
  have validationPositive : 0 < options.limits.validation := by
    have h := input.contract.resources.configuredFuel.2.2.2
    unfold work at h
    omega
  have dispatchPositive : 0 < limits.callDispatch := by
    have h := input.contract.resources.executionFuel.1
    unfold work at h
    omega
  have validSource : (1 : MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have validDest : RootReferenceFacts.destination true < frame.locals.size := by rw [size]; decide
  have valid11 : 11 < frame.locals.size := by rw [size]; decide
  have sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
        (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm) := by
    have h := congrArg LocalState.value (Option.some.inj (by simpa [Array.getElem?_eq_getElem validSource] using sourceCell))
    rw [CanonicalConfigFacts.actual_access_runtime options () remaining span,
      CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span] at *
    exact h
  have sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference := by
    exact congrArg LocalState.layout (Option.some.inj (by simpa [Array.getElem?_eq_getElem validSource] using sourceCell))
  have lenLive : frame.locals[11].value = .live (.immediate .uninit) := by
    exact congrArg LocalState.value (Option.some.inj (by simpa [Array.getElem?_eq_getElem valid11] using lenCell))
  have lenUncached : frame.locals[11].layout = none := by
    exact congrArg LocalState.layout (Option.some.inj (by simpa [Array.getElem?_eq_getElem valid11] using lenCell))
  have destCellValid : (12 : MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have destLive : frame.locals[RootReferenceFacts.destination true].value = .live (.immediate .uninit) := by
    have h := congrArg LocalState.value (Option.some.inj (by simpa [Array.getElem?_eq_getElem destCellValid] using exprCell))
    simpa [RootReferenceFacts.destination] using h
  have destUncached : frame.locals[RootReferenceFacts.destination true].layout = none := by
    have h := congrArg LocalState.layout (Option.some.inj (by simpa [Array.getElem?_eq_getElem destCellValid] using exprCell))
    simpa [RootReferenceFacts.destination] using h
  obtain ⟨result,post,_tree,_held,_child,lenTrace,resultEq,_memory,_borrow,_runtime,_range,
    _ghost,_shallow,_race2,_address2,_types2,_extras2,_backend2,_unchecked2,_noGc2,_fixed2,_thread2⟩ :=
    GeneralBorrowRawSharedToLen.complete options limits remaining span
      input.contract.model.preciseOff input.contract.model.implicitOff input.contract.model.debugOff
      input.contract.model.nullComparator (options.place.dynamicFuel-1) (options.limits.validation-1)
      (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
      reference.base reference.offset len reference.id sourceEntry positive nonzero signedFits #[] frame current
      body identity callee located tracker enabled mode fresh reference.tracker.global.nextPointerTag
      runtime raw rawTag rawOffset rawLen capacity validSource validDest sourceLive sourceCached
      destLive destUncached noClocks ghost shallow cached present race metadata notConstructed
      shortRoom nodeRoom tagRoom rfl (limits.callDispatch-1) (Nat.sub_add_cancel dispatchPositive).symm
      (DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model)
      valid11 lenLive lenUncached backend unchecked noGc fixed thread active topZero
  refine ⟨entry,frame,result,machine,post,actual,prefixTrace,lenTrace,?_⟩
  rw [resultEq]
  simp [LenCallResultFrame.resultFrame,GeneralBorrowForestSharedPreLenFrame.after]

end
end DuplicatePrefix.S02SeparateDestinationActualSharedLen

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationActualSharedLen.executes) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual shared length dependency {dependency}"
