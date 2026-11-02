import duplicate_prefix.GeneralBorrowRawRootZeroEntry
namespace DuplicatePrefix.GeneralBorrowRawRootInitialize
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
private theorem untick (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (facts : GenericSharedLenAccepted.RuntimeFacts options remaining span before (RootZeroCompleteState.tick options remaining span machine)) :
    GenericSharedLenAccepted.RuntimeFacts options remaining span before machine := by
  have data : (RootZeroCompleteState.tick options remaining span machine).user.addresses=machine.user.addresses ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.types=machine.user.payload.payload.user.types ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.backend=machine.user.payload.payload.user.backend := by
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl⟩
  exact ⟨(RootZeroCompleteState.tick_ghost options remaining span machine).symm.trans facts.ghost,
    (RootZeroCompleteState.tick_shallow options remaining span machine).symm.trans facts.shallow,
    facts.race,data.1.symm.trans facts.addresses,data.2.1.symm.trans facts.types,data.2.2.1.symm.trans facts.extras,
    data.2.2.2.symm.trans facts.backend,
    (RootZeroCompleteState.tick_flags options remaining span machine).1.symm.trans facts.unchecked,
    (RootZeroCompleteState.tick_flags options remaining span machine).2.symm.trans facts.noGc,facts.fixed,facts.active⟩

noncomputable def caller (s : GeneralBorrowRawRootZeroEntry.Initial) (n : UInt64) : CompilerFrameContext.ActualFrame :=
  PositiveRootInstalledFrame.installed (RawRootInvocation.root s.before s.place s.race)
    (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
      (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset)))
      s.len ActualReferenceMetadata.reference).imm n {} s.id s.tracker.global.nextPointerTag s.slotId
    (next s.tracker s.fresh).global.nextPointerTag

/-- Genuine ROOT initialization for every count using the SAME count-free
initial contract as the complete zero branch. The returned raw release data,
physical frame facts and runtime facts are derived from that initial state. -/
theorem initializes (s : GeneralBorrowRawRootZeroEntry.Initial) (n : UInt64) :
    ∃ (frame : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (release : GeneralBorrowRawRootReleasePlan.Input machine.memory
        (held s.tracker s.fresh s.slotFresh).global),
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second n)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ =
        .ok () (Storage.withCurrent #[] frame machine) ∧
      machine.borrowTracker = some (held s.tracker s.fresh s.slotFresh) ∧
      GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before machine ∧
      frame.location = .mir ⟨0,0⟩ ∧ frame.locals.size = 25 ∧
      frame.body = RootBody.reflected.body.body ∧
      frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩ ∧
      frame.extra.borrowTracker = some (GeneralBorrowRawRootReleasePlan.frame release) ∧
      release.id = s.id ∧ release.tag = s.tracker.global.nextPointerTag ∧ release.slotId = s.slotId ∧
      release.slotRoot = s.slotRoot ∧ release.slotChild = (next s.tracker s.fresh).global.nextPointerTag ∧
      release.slot.allocation.byteSize = Size.ofBytes 1 ∧ release.slot.allocation.len = 1 ∧
      release.slot.allocation.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      release.slot.allocation.provenanceMap = ProvenanceMap.new ∧ release.slot.allocation.mutability = .Mut ∧
      frame = caller s n ∧
      machine = enteredMachine (RawRootInvocation.machine #[] s.before) s.tracker s.fresh s.id s.entry s.parentTag
        s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot release.slot.allocation := by
  obtain ⟨updated,call,slotTree,slotSize,slotLen,slotMask,slotProv,slotBytes,slotMut⟩ :=
    GeneralBorrowRawRootInvocation.enters s.options s.limits s.remaining s.span s.ctx s.debugOff s.cmp s.dynamicFuel s.validityFuel
      s.fuelEq s.validationEq s.id s.parentTag s.tracker s.base s.offset s.len n s.nonzero s.entry s.positive s.signedFits s.bounds
      s.before s.ghost s.shallow s.cachedAddress s.present s.enabled s.fresh s.runtime s.raw s.rawTag s.rawOffset s.rawLen s.capacity s.race s.metadata s.notConstructed
      s.retagCtx s.place s.layout s.slotId s.slotEntry s.slotBase s.slotRoot s.slotPointer s.aligned s.slotCached s.slotTree s.slotSize
      s.slotPresent s.separate s.slotFresh s.slotDistinct s.slotParentDistinct s.slotFree s.mutable s.storage s.maskLength s.provenance
      s.noBackend s.extras s.thread s.active s.noCache
  let raw := RawRootInvocation.root s.before s.place s.race
  let rawMachine := RawRootInvocation.machine #[] s.before
  let adjusted := (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
    (Pointer.new (.concrete s.id s.tracker.global.nextPointerTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm
  let tag := (next s.tracker s.fresh).global.nextPointerTag
  let tracker := held s.tracker s.fresh s.slotFresh
  let frame := PositiveRootInstalledFrame.installed raw adjusted n {} s.id s.tracker.global.nextPointerTag s.slotId tag
  let machine := enteredMachine rawMachine s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot updated
  change _ = (EStateM.Result.ok () (Storage.withCurrent #[] frame machine) : EStateM.Result StepError RootState Unit) at call
  have runtime := untick s.options s.remaining s.span s.before machine
    (GenericFunctionEntryRuntime.facts s.options s.remaining s.span s.before s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len
      s.slotFresh s.slotId s.slotEntry s.slotRoot updated s.ghost s.shallow s.race s.noBackend s.thread s.active s.unchecked s.noGc s.fixed)
  obtain ⟨fb,fi,fc,frc,frp,fva,frace,fborrow,floc⟩ := PositiveRootInstalledFrame.metadata raw adjusted n {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have fsize := PositiveRootInstalledFrame.size raw adjusted n {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have slots (i : Fin 25) := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals s.before s.place s.race)
    adjusted n {} s.id s.tracker.global.nextPointerTag s.slotId tag i
  let fixedRaw : GeneralBorrowRawFnEntry.Input s.entry.allocation.extra s.tracker.global :=
    {s.raw with
      parentTag:=s.parentTag,offset:=s.offset,len:=s.len,
      tagged:=by rw [←s.rawTag];exact s.raw.tagged,
      positive:=by simpa only [s.rawOffset,s.rawLen] using s.raw.positive}
  have described : ∃ release : GeneralBorrowRawRootReleasePlan.Input machine.memory tracker.global,
      release.id = s.id ∧ release.tag = s.tracker.global.nextPointerTag ∧ release.slotId = s.slotId ∧
      release.slot = (⟨s.slotEntry.kind,updated⟩ : LocalAllocation Provenance BorrowTree MiriMemoryKind) ∧
      release.slotRoot = s.slotRoot ∧ release.slotChild = tag := by
    exact
      (GeneralBorrowRawRootReleaseDescribed.described #[] raw.frame rawMachine s.tracker s.id s.slotId
        s.entry s.slotEntry s.runtime fixedRaw s.nodeHeadroom {} s.separate s.slotFresh s.slotRoot
        s.slotFree s.slotParentDistinct s.slotDistinct updated slotTree)
  obtain ⟨release,releaseId,releaseTag,releaseSlotId,releaseSlot,releaseRoot,releaseChild⟩ := described
  refine ⟨frame,machine,release,call,rfl,runtime,floc,fsize,fb.trans raw.body,?_,?_,releaseId,releaseTag,releaseSlotId,
    releaseRoot,releaseChild,?_,?_,?_,?_,?_,rfl,?_⟩
  · simpa using slots ⟨2,by decide⟩
  · rw [GeneralBorrowRawRootReleasePlan.frame,releaseId,releaseTag,releaseSlotId,releaseChild]
    exact fborrow
  · rw [releaseSlot];exact slotSize
  · rw [releaseSlot];exact slotLen
  · rw [releaseSlot];exact slotMask
  · rw [releaseSlot];exact slotProv
  · rw [releaseSlot];exact slotMut
  · rw [releaseSlot]
end
end DuplicatePrefix.GeneralBorrowRawRootInitialize
