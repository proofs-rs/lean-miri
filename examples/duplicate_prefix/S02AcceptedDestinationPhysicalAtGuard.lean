import duplicate_prefix.S02AcceptedDefaultReadyComplete
import duplicate_prefix.S02SeparateDestinationZeroCoreTagged
import duplicate_prefix.S02SeparateDestinationRejectedPhysicalTransport
import duplicate_prefix.S02SeparateDestinationPhysicalIdentity
import duplicate_prefix.S02SeparateDestinationStateJoin

namespace DuplicatePrefix.S02AcceptedDestinationPhysicalAtGuard
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The original physical return place survives the accepted Ref/len guard,
on the exact installed call state, before the source copy. -/
theorem at_guard
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
    ∃ (entry result : CompilerFrameContext.ActualFrame)
      (initial post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry initial) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry initial) (Storage.withCurrent #[] result post) ∧
      result.location = .mir ⟨6,7⟩ ∧
      Nonempty (S03FinalReturnInputBounds.Destination post place) := by
  obtain ⟨entry,result,initial,post,reference,sourceEntry,tracker,sourceRaw,finalTree,held,raw,
    actual,trace,located,_size,_body,_identity,_callee,_slot13,_slot15,_slot16,_immediate,_extraEq,_trackEq,
    _noClocks,_slot0,_sourceCell,_countCell,_high,memory,_oldActivity,_storage,_maskValid,_maskLen,
    _initialized,_provenance,_storageFits,_mutable,_sourceExtras,_initialTracked,_postTracked,_modeEq,
    _ghost,_shallow,_race,addresses,_types,_extras,_backend,_unchecked,_noGc,_fixed,_thread,
    _runtime,_graph,_positive,_nonzero,_signed,_bounds,_sourceCapacity,_nodeMargin,_tagMargin,
    _rawTag,_rawOffset,_rawLen⟩ :=
    S02AcceptedDefaultReadyComplete.after_guard_complete id tag address len count input nonempty different
      returnTag returnConcrete countPositive within
  obtain ⟨packetFrame,packetMachine,packetActual,packet,_sourceSame⟩ :=
    S02SeparateDestinationZeroCoreTagged.enters id tag address len count input nonempty different
      returnTag returnConcrete
  have same : Storage.withCurrent #[] packetFrame packetMachine = Storage.withCurrent #[] entry initial :=
    (EStateM.Result.ok.inj (packetActual.symm.trans actual)).2
  have machineEq : packetMachine = initial :=
    S02SeparateDestinationPacketJoin.same_machine packetFrame entry packetMachine initial same
  have physicalId : packet.destination.id = input.contract.destination.id :=
    (S02SeparateDestinationPhysicalIdentity.original input.contract.destination packet.destination
      returnTag returnConcrete).1
  have differentDest : reference.id ≠ packet.destination.id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    rw [←binding.1,physicalId]
    exact different
  have tickMemory := (S02SeparateDestinationTickLedger.preserved options remaining span initial).1
  have tickAddresses := (S02SeparateDestinationTickLedger.preserved options remaining span initial).2.2.2.2.1
  have memoryTick : post.memory = RetagEntry.updatedMemory
      (RootZeroCompleteState.tick options remaining span initial).memory reference.id sourceEntry finalTree := by
    rw [tickMemory]
    exact memory
  have addressesTick : post.user.addresses = (RootZeroCompleteState.tick options remaining span initial).user.addresses := by
    rw [tickAddresses]
    exact addresses
  let original : S03FinalReturnInputBounds.Destination initial place := machineEq ▸ packet.destination
  have originalId : original.id = packet.destination.id := by
    cases machineEq
    rfl
  let destination := S02SeparateDestinationRejectedPhysicalTransport.after_body options remaining span
    original reference.id sourceEntry finalTree (by simpa only [originalId] using differentDest) memoryTick addressesTick
  exact ⟨entry,result,initial,post,actual,trace,located,⟨destination⟩⟩

end
end DuplicatePrefix.S02AcceptedDestinationPhysicalAtGuard

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02AcceptedDestinationPhysicalAtGuard.at_guard) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved accepted destination physical guard dependency {dependency}"
