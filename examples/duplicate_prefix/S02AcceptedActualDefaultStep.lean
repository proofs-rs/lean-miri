import duplicate_prefix.S02AcceptedDefaultReadyGraph
import duplicate_prefix.S02AcceptedDefaultResourceBridge
import duplicate_prefix.S02SeparateDestinationMachineGeometry
import duplicate_prefix.GeneralBorrowRawDefaultExpression

namespace DuplicatePrefix.S02AcceptedActualDefaultStep
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The accepted positive concrete, separate-allocation call reaches MIR 6,7
and executes its real Default mutable-reference step. The subsequent as_mut
call and physical copy are separate obligations. -/
theorem actual_step
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
    (countPositive : 0 < count.toNat) (within : count ≤ len/2) :
    ∃ (entry result nextFrame : CompilerFrameContext.ActualFrame)
      (initial post nextMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry initial) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry initial) (Storage.withCurrent #[] result post) ∧
      result.location = .mir ⟨6,7⟩ ∧
      ExecutionMachine.step (config options (remaining+1) span) limits ()
        (Storage.withCurrent #[] result post) =
          (Storage.withCurrent #[] nextFrame nextMachine,.ok true) := by
  obtain ⟨entry,result,initial,post,reference,sourceEntry,tracker,sourceRaw,finalTree,held,raw,
    actual,trace,located,size,body,identity,callee,slot13,slot15,slot16,immediate,extraEq,trackEq,
    noClocks,sourceCell,countCell,high,memory,initialTracked,postTracked,modeEq,
    ghost,shallow,race,addresses,types,extras,backend,unchecked,noGc,fixed,thread,
    runtime,graph,positive,nonzero,signed,bounds,sourceCapacity,nodeMargin,tagMargin,rawTag,rawOffset,rawLen⟩ :=
    S02AcceptedDefaultReadyGraph.after_guard_graph id tag address len count input nonempty different
      returnTag returnConcrete countPositive within
  let buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {sourceEntry with allocation := sourceEntry.allocation.setExtra finalTree}
  have refId : reference.id = id := by
    have h := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at h
    exact h.1.symm
  have postMemory : post.memory = RetagEntry.updatedMemory initial.memory id sourceEntry finalTree := by
    simpa only [refId] using memory
  have present : post.memory.live.find? (fun row => row.1 == id) = some (id,buffer) := by
    rw [postMemory]
    exact StackPopRelease.lookup_commit_same initial.memory id sourceEntry finalTree
  have capacity : buffer.allocation.extra.locations.size = buffer.allocation.byteSize := by
    change finalTree.locations.size = sourceEntry.allocation.byteSize
    exact graph.capacity.trans sourceCapacity
  obtain ⟨_ref2,tracker2,installed2,initial2,actual2,tracked2,mode2,_ghost2,_shallow2,
    _unchecked2,_noGc2,_fixed2,_race2,addr2,types2,_backend2,_thread2⟩ :=
    S02SeparateDestinationMachineGeometry.after_exact id tag address len count input nonempty different
      returnTag returnConcrete
  have same : Storage.withCurrent #[] installed2 initial2 = Storage.withCurrent #[] entry initial :=
    (EStateM.Result.ok.inj (actual2.symm.trans actual)).2
  have initialEq : initial2 = initial := congrArg (fun s : RootState => s.machine) same
  have trackerEq : tracker2 = tracker :=
    Option.some.inj (by rw [initialEq] at tracked2; exact tracked2.symm.trans initialTracked)
  have defaultMode : held.retagMode = .Default := modeEq.trans (trackerEq ▸ mode2)
  have fresh : held.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change held.global.nextPointerTag.value.toNat < 18446744073709551615
    have h := (S02AcceptedDefaultResourceBridge.after_shared sourceEntry.allocation.extra finalTree
      tracker held sourceRaw.selected graph nodeMargin tagMargin).2
    omega
  have cachedAddress : post.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,reference.base⟩ := by
    rw [addresses,←initialEq,addr2]
    simpa only [refId] using reference.cachedBase
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] result post)).metadata = PreparedReflection.actual.runtime := by
    change post.user.payload.payload.user.types.metadata = _
    rw [types,←initialEq,types2]
    exact input.contract.model.metadata
  have notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] result post)).entries.any (·.value.ty == 4) = false := by
    change post.user.payload.payload.user.types.entries.any (·.value.ty == 4) = _
    rw [types,←initialEq,types2]
    exact input.slice_not_constructed
  have dynamicPositive : 0 < options.place.dynamicFuel := by
    have h := input.contract.resources.dynamicFuel
    unfold work at h
    omega
  have validationPositive : 0 < options.limits.validation := by
    have h := input.contract.resources.configuredFuel.2.2.2
    unfold work at h
    omega
  have valid1 : (1 : MIR.LocalId) < result.locals.size := by rw [size]; decide
  have valid16 : (16 : MIR.LocalId) < result.locals.size := by rw [size]; decide
  have cell (i : Nat) (valid : i < result.locals.size)
      (row : LocalState Provenance LocalLayout) (h : result.locals[i]? = some row) :
      result.locals[i] = row :=
    Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans h)
  have sourceLive : result.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id raw.parentTag) (Size.ofBytes (reference.base+reference.offset)))
      len ActualReferenceMetadata.reference).imm) := by
    have h := congrArg LocalState.value (cell 1 valid1 _ sourceCell)
    rw [rawTag,refId,CanonicalConfigFacts.actual_access_runtime options () remaining span,
      CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span] at *
    exact h
  have sourceCached : result.locals[1].layout = some ActualReferenceMetadata.reference :=
    congrArg LocalState.layout (cell 1 valid1 _ sourceCell)
  have destLive : result.locals[16].value = .live (.immediate .uninit) :=
    congrArg LocalState.value (cell 16 valid16 _ slot16)
  have destUncached : result.locals[16].layout = none :=
    congrArg LocalState.layout (cell 16 valid16 _ slot16)
  have step := GeneralBorrowRawDefaultExpression.positive_statement options limits remaining span
    input.contract.model.preciseOff input.contract.model.implicitOff input.contract.model.debugOff
    input.contract.model.nullComparator (options.place.dynamicFuel-1) (options.limits.validation-1)
    (Nat.sub_add_cancel dynamicPositive).symm (Nat.sub_add_cancel validationPositive).symm
    reference.base reference.offset len id buffer positive nonzero signed #[] result post
    body identity callee located held postTracked defaultMode fresh raw.parentTag runtime raw
    rfl rawOffset rawLen capacity valid1 valid16 sourceLive sourceCached destLive destUncached
    noClocks ghost shallow cachedAddress present race metadata notConstructed
  exact ⟨entry,result,_,initial,post,_,actual,trace,located,step⟩

end
end DuplicatePrefix.S02AcceptedActualDefaultStep

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02AcceptedActualDefaultStep.actual_step) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual Default step dependency {dependency}"
