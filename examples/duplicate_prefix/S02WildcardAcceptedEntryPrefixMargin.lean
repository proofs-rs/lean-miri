import duplicate_prefix.S02WildcardAcceptedCoreCapacity
import duplicate_prefix.S02SeparateDestinationRejectedPurePrefix
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.AsMutPushPreserves
import duplicate_prefix.S03ZeroCountBodyActiveSeparateBounds

namespace DuplicatePrefix.S02WildcardAcceptedEntryPrefixMargin
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual wildcard accepted prefix reaches shared Ref with source capacity
and node/tag reserves retained on the same installed packet. -/
theorem executes
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (countPositive : 0 < count.toNat)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
    ∃ (entry : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (packet : S02SeparateDestinationZeroCore.Packet entry machine place)
      (raw : GeneralBorrowRawShared.Input packet.sourceEntry.allocation.extra packet.tracker.global)
      (frame : CompilerFrameContext.ActualFrame),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine) ∧
      raw.parentTag = reference.tracker.global.nextPointerTag ∧
      raw.parent = packet.sourceChild ∧ raw.offset = reference.offset ∧ raw.len = len ∧
      packet.sourceId = reference.id ∧ raw.selected = packet.sourceChild ∧
      raw.maximum = some reference.tracker.global.nextPointerTag ∧
      packet.sourceTag = reference.tracker.global.nextPointerTag ∧
      packet.sourceSelected = packet.sourceChild ∧
      packet.sourceMaximum = some reference.tracker.global.nextPointerTag ∧
      packet.sourceOffset = reference.offset ∧ packet.sourceLen = len ∧
      entry = PositiveRootInstalledFrame.installed
        (RawRootInvocation.root before place input.contract.model.noDataRace)
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
            (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
        count {} reference.id reference.tracker.global.nextPointerTag
        packet.destination.id packet.returnTag ∧
      machine.user = (RawRootInvocation.machine #[] before).user ∧
      machine.threads = (RawRootInvocation.machine #[] before).threads ∧
      machine.dataRace = (RawRootInvocation.machine #[] before).dataRace ∧
      packet.tracker.retagMode = .Default ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry machine)
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span machine)) ∧
      GenericFunctionEntryPrefix.Shape entry frame count ∧
      packet.sourceEntry.allocation.extra.locations.size = packet.sourceEntry.allocation.byteSize ∧
      reference.offset.toNat+len.toNat ≤ packet.sourceEntry.allocation.byteSize.bytes.toNat ∧
      packet.sourceEntry.allocation.extra.nodes.size+4 < 65536 ∧
      packet.tracker.global.nextPointerTag.value.toNat+3 < 18446744073709551615 := by
  obtain ⟨reference,ready⟩ := S02WildcardAcceptedCoreCapacity.enters address len count input nonempty
    returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨frame,machine,actual,packet,raw,frameLiteral,rawUser,rawThreads,rawRace,packetMode,
    rawTag,rawParent,rawOffset,rawLen,sourceId,rawSelected,rawMaximum,
    sourceTag,sourceSelected,sourceMaximum,sourceOffset,sourceLen,
    capacity,bounds,nodes,tagRoom⟩ :=
    ready different
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  have frameMetadata := PositiveRootInstalledFrame.metadata root adjusted count {}
    reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag
  have frameSize' := PositiveRootInstalledFrame.size root adjusted count {}
    reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag
  have frameSlots := PositiveRootInstalledFrame.slot_option root
    (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted count {}
    reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag
  have immediate' := PositiveRootInstalledFrame.immediate root
    (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted count {}
    reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag
  have frameSize : frame.locals.size = 25 := by rw [frameLiteral];exact frameSize'
  have slot0 : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by
    rw [frameLiteral];simpa using frameSlots ⟨0,by decide⟩
  have slot2 : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := by
    rw [frameLiteral];simpa using frameSlots ⟨2,by decide⟩
  have slot3 : frame.locals[3]? = some ⟨.dead,none⟩ := by
    rw [frameLiteral];simpa using frameSlots ⟨3,by decide⟩
  have slot4 : frame.locals[4]? = some ⟨.dead,none⟩ := by
    rw [frameLiteral];simpa using frameSlots ⟨4,by decide⟩
  have slot5 : frame.locals[5]? = some ⟨.dead,none⟩ := by
    rw [frameLiteral];simpa using frameSlots ⟨5,by decide⟩
  have body : frame.body = RootBody.reflected.body.body := by
    rw [frameLiteral];exact frameMetadata.1
  have identity : frame.bodyIdentity = RootBody.reflected.body.identity := by
    rw [frameLiteral];exact frameMetadata.2.1
  have callee : frame.functionInstance = RootBody.reflected.functionInstance := by
    rw [frameLiteral];exact frameMetadata.2.2.1
  have location : frame.location = .mir ⟨0,0⟩ := by
    rw [frameLiteral];exact frameMetadata.2.2.2.2.2.2.2.2
  have noLocalClocks : frame.extra.dataRace = none := by
    rw [frameLiteral]
    exact frameMetadata.2.2.2.2.2.2.1.trans root.noClocks
  have returnPlace : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [frameLiteral,frameMetadata.2.2.2.2.1]
    rfl
  have continuation : frame.returnContinuation = .stop true := by
    rw [frameLiteral,frameMetadata.2.2.2.1]
    rfl
  have immediateLocals : CopyHelperCleanup.AllImmediate frame := by
    rw [frameLiteral];exact immediate'
  have varargs : frame.vaList = #[] := by
    rw [frameLiteral,frameMetadata.2.2.2.2.2.1]
    rfl
  have rawActive : (RawRootInvocation.machine #[] before).threads.activeThread? =
      some {input.contract.thread with topUserRelevantFrame := some 0} := by
    change (CallEntryFacts.cacheTop (CallEntryFacts.freshRoot before).1 0).threads.activeThread? = _
    exact AsMutPushPreserves.active_cache (CallEntryFacts.freshRoot before).1 input.contract.thread
      (by simpa only [CallEntryFacts.freshRoot] using input.contract.active) 0
  have active : machine.threads.activeThread? =
      some {input.contract.thread with topUserRelevantFrame := some 0} := by
    rw [rawThreads];exact rawActive
  obtain ⟨_,_,raceEq,_addressesEq,ghostEq,shallowEq,_typesEq,backendEq,_⟩ :=
    RawRootInvocation.preservation #[] before
  have race : machine.dataRace = none := by
    rw [rawRace,raceEq];exact input.contract.model.noDataRace
  have backend : machine.user.payload.payload.user.backend = .none := by
    rw [rawUser,backendEq];exact input.contract.model.noBackend
  have ghost : machine.user.payload.ghost = false := by
    rw [rawUser,ghostEq];exact input.contract.model.ghostOff
  have shallow : machine.user.payload.validation = .Shallow := by
    rw [rawUser,shallowEq];exact input.contract.model.shallow
  have unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false := by
    rw [rawUser,RootZeroInvocationState.raw_control];exact input.contract.model.unchecked
  have noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0 := by
    rw [rawUser,RootZeroInvocationState.raw_control];exact input.contract.model.noGc
  have fixed : machine.threads.fixedScheduling = true := by
    rw [rawThreads]
    change before.threads.fixedScheduling = true
    exact input.contract.model.fixedScheduler
  have fuelPositive : 0 < options.limits.validation := by
    have bound := input.contract.resources.configuredFuel.2.2.2
    unfold DuplicatePrefixCallSpecification.work at bound
    omega
  let fuel := options.limits.validation - 1
  have validationFuel : options.limits.validation = fuel+1 := by dsimp only [fuel];omega
  have debugOff : options.place.debugAssertions = false := input.contract.model.debugOff
  have nonzero : count ≠ 0 := by
    intro zero
    rw [zero] at countPositive
    simp at countPositive
  have slots : ∀ i : Fin 25, frame.locals[i.val]? = some (
      if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
      else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
      else if 1 = i.val then ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩
      else ⟨.dead,none⟩) := by
    intro i
    rw [frameLiteral]
    exact frameSlots i
  have source := DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model
  obtain ⟨next,trace,shape⟩ :=
    S02SeparateDestinationRejectedPurePrefix.executes_from_installed_locals options limits remaining span
      source debugOff fuel validationFuel frame machine count nonzero body identity callee location
      frameSize adjusted slots noLocalClocks immediateLocals packet.tracker packet.enabled
      packetMode ghost shallow unchecked noGc fixed
  exact ⟨frame,machine,packet,raw,next,actual,rawTag,rawParent,rawOffset,rawLen,
    sourceId,rawSelected,rawMaximum,sourceTag,sourceSelected,sourceMaximum,sourceOffset,sourceLen,
    frameLiteral,rawUser,rawThreads,rawRace,packetMode,trace,shape,
    capacity,bounds,nodes,tagRoom⟩

end
end DuplicatePrefix.S02WildcardAcceptedEntryPrefixMargin

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardAcceptedEntryPrefixMargin.executes) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard rejected-entry-prefix capacity dependency {dependency}"
