import duplicate_prefix.S02WildcardZeroCoreSettings
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.AsMutPushPreserves
import duplicate_prefix.S03ZeroCountBodyActiveSeparateBounds

namespace DuplicatePrefix.S02WildcardZeroBody
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The original positive wildcard call reaches normal Return without UB for
count zero when its resolved source and concrete return allocation differ. -/
theorem executes
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
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
      ⟨cfg,limits,fun _ _ => True⟩
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
    ∃ installed done,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second 0)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace cfg limits installed done ∧
      ExecutionMachine.step cfg limits () done = (done,.ok false) ∧ done.stack.frames = #[] ∧
      CallSafety.NoErrorsBeforeReturn safety 1 installed ∧
      CallSafety.NoUBBeforeReturn safety 1 installed := by
  obtain ⟨reference,ready⟩ := S02WildcardZeroCoreSettings.enters address len 0 input nonempty
    returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨frame,machine,actual,packet,frameLiteral,rawUser,rawThreads,rawRace,packetMode⟩ :=
    ready different
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  have frameMetadata := PositiveRootInstalledFrame.metadata root adjusted 0 {}
    reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag
  have frameSize' := PositiveRootInstalledFrame.size root adjusted 0 {}
    reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag
  have frameSlots := PositiveRootInstalledFrame.slot_option root
    (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted 0 {}
    reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag
  have immediate' := PositiveRootInstalledFrame.immediate root
    (RawRootInvocation.locals before place input.contract.model.noDataRace) adjusted 0 {}
    reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag
  have frameSize : frame.locals.size = 25 := by rw [frameLiteral];exact frameSize'
  have slot0 : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ := by
    rw [frameLiteral];simpa using frameSlots ⟨0,by decide⟩
  have slot2 : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩ := by
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
  have physicalId : packet.destination.id = input.contract.destination.id :=
    (S02SeparateDestinationPhysicalIdentity.original input.contract.destination packet.destination
      returnTag returnConcrete).1
  have extras : machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == packet.destination.id) = some (packet.destination.id,⟨none,#[]⟩) := by
    rw [physicalId,rawUser]
    change (RawRootInvocation.machine #[] before).user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == input.contract.destination.id) = _
    rw [(RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2]
    exact input.return_extras
  have outside : ∀ row ∈ (#[] : Array (Size × MemoryExtras.Entry Unit)),
      row.1.bytes.toNat < packet.destination.offset.toNat ∨
        packet.destination.offset.toNat + 1 ≤ row.1.bytes.toNat := by simp
  have slot0Row : frame.locals[0]'(by rw [frameSize];decide) =
      ⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot0)
  have slot2Row : frame.locals[2]'(by rw [frameSize];decide) =
      ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot2)
  have slot3Row : frame.locals[3]'(by rw [frameSize];decide) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot3)
  have slot4Row : frame.locals[4]'(by rw [frameSize];decide) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot4)
  have slot5Row : frame.locals[5]'(by rw [frameSize];decide) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    Option.some.inj ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).symm.trans slot5)
  have source := DuplicatePrefixCallModel.sourceComparator options remaining span before input.contract.model
  obtain ⟨done,trace,terminal,empty,noErrors,noUB⟩ :=
    S03ZeroCountBodyActiveSeparateBounds.complete_active_separate options limits remaining span
      frame machine packet.tracker packet.borrowFrame packetMode packet.enabled packet.frameTracked
      place packet.destination packet.returnTag packet.child packet.selected packet.maximum packet.returnNode
      packet.sourceId packet.sourceEntry packet.separate packet.sourceLive packet.sourceTag
      packet.sourceChild packet.sourceSelected packet.sourceMaximum packet.sourceOffset packet.sourceLen
      packet.sourceNode packet.sourceTagged packet.sourcePresent packet.sourceHidden packet.sourceRuntime
      packet.sourcePositive packet.sourceDistinct packet.sourceOrder packet.sourceShort packet.sourceActivity
      packet.owned packet.returnTagged packet.returnPresent packet.returnSame packet.returnEdge
      packet.returnHidden packet.hiddenFrame packet.runtime packet.positive packet.distinct packet.order
      packet.short packet.activity {input.contract.thread with topUserRelevantFrame := some 0} active
      race backend ghost shallow
      #[] extras outside fuel debugOff validationFuel source
      body identity callee location
      frameSize (congrArg LocalState.value slot0Row)
      (congrArg LocalState.layout slot0Row) (congrArg LocalState.value slot3Row)
      (congrArg LocalState.value slot4Row) (congrArg LocalState.value slot5Row)
      (congrArg LocalState.layout slot4Row) (congrArg LocalState.layout slot5Row)
      (congrArg LocalState.value slot2Row) (congrArg LocalState.layout slot2Row)
      noLocalClocks returnPlace continuation immediateLocals varargs
      unchecked noGc fixed
  exact ⟨Storage.withCurrent #[] frame machine,done,actual,trace,terminal,empty,noErrors,noUB⟩

end
end DuplicatePrefix.S02WildcardZeroBody

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardZeroBody.executes) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard zero-body dependency {dependency}"
