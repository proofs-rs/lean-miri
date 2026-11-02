import duplicate_prefix.GeneralBorrowRawRootZeroEntry
import duplicate_prefix.GeneralBorrowRawRootReleaseDescribed
import duplicate_prefix.GeneralBorrowRawRootInvocation
import duplicate_prefix.GenericFunctionEntryRuntime
import duplicate_prefix.GenericFunctionEntryNumerics
import duplicate_prefix.GeneralBorrowRawRootZeroPhysical
import duplicate_prefix.PositiveRootInstalledFrame
namespace DuplicatePrefix.GeneralBorrowRawRootZeroDescribed
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial

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

/-- Form the zero-count physical-return contract from the original caller state
and a genuine root call. Positive slice length and all caller/configuration,
graph/ownership/allocator/return-storage hypotheses are explicit in Initial.
No intermediate operation, release plan or successful invocation is an input. -/
theorem prepare (s : Initial) :
    ∃ input : GeneralBorrowRawRootZeroPhysical.Input,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧ input.release.slotId=s.slotId ∧ input.context=s.writeContext ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second 0)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ =
        .ok () (Storage.withCurrent #[] input.before input.machine) := by
  obtain ⟨updated,call,slotTree,slotSize,slotLen,slotMask,slotProv,slotBytes,slotMut⟩ :=
    GeneralBorrowRawRootInvocation.enters s.options s.limits s.remaining s.span s.ctx s.debugOff s.cmp s.dynamicFuel s.validityFuel
      s.fuelEq s.validationEq s.id s.parentTag s.tracker s.base s.offset s.len 0 s.nonzero s.entry s.positive s.signedFits s.bounds
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
  let frame := PositiveRootInstalledFrame.installed raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag
  let machine := enteredMachine rawMachine s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len s.slotFresh s.slotId s.slotEntry s.slotRoot updated
  change _ = (EStateM.Result.ok () (Storage.withCurrent #[] frame machine) : EStateM.Result StepError RootState Unit) at call
  have runtime := untick s.options s.remaining s.span s.before machine
    (GenericFunctionEntryRuntime.facts s.options s.remaining s.span s.before s.tracker s.fresh s.id s.entry s.parentTag s.offset s.len
      s.slotFresh s.slotId s.slotEntry s.slotRoot updated s.ghost s.shallow s.race s.noBackend s.thread s.active s.unchecked s.noGc s.fixed)
  obtain ⟨fb,fi,fc,frc,frp,fva,frace,fborrow,floc⟩ := PositiveRootInstalledFrame.metadata raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have fsize := PositiveRootInstalledFrame.size raw adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag
  have slots (i : Fin 25) := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals s.before s.place s.race)
    adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag i
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
  obtain ⟨thread,active,top⟩ := runtime.active
  let input : GeneralBorrowRawRootZeroPhysical.Input := {
    options:=s.options,limits:=s.limits,remaining:=s.remaining,span:=s.span,source:=s.source,fuel:=s.validityFuel,
    debugOff:=s.debugOff,validationFuel:=s.validationEq,context:=s.writeContext,validationContext:=s.validationContext,
    accessEq:=s.accessEq,validationWidth:=s.validationWidth,validationRuntimeSize:=s.validationRuntimeSize,sameRuntime:=s.sameRuntime,
    width:=s.width,runtimeWidth:=s.runtimeWidth,runtimeSize:=s.runtimeSize,outerAccessEq:=s.outerAccessEq,
    before:=frame,size:=fsize,location:=floc,slot0:=by simpa using slots ⟨0,by decide⟩,
    slot3:=by simpa using slots ⟨3,by decide⟩,slot4:=by simpa using slots ⟨4,by decide⟩,slot5:=by simpa using slots ⟨5,by decide⟩,
    slot2:=by simpa using slots ⟨2,by decide⟩,
    immediate:=PositiveRootInstalledFrame.immediate raw (RawRootInvocation.locals s.before s.place s.race) adjusted 0 {} s.id s.tracker.global.nextPointerTag s.slotId tag,
    body:=fb.trans raw.body,identity:=fi.trans raw.identity,callee:=fc.trans raw.callee,noLocalClocks:=frace.trans raw.noClocks,
    continuation:=frc.trans (RawRootInvocation.control s.before s.place s.race).2.2.1,varargs:=by rw [fva];rfl,
    machine:=machine,tracker:=tracker,tracked:=rfl,defaultMode:=s.mode,noClocks:=runtime.race,noBackend:=runtime.backend,
    ghost:=runtime.ghost,shallow:=runtime.shallow,unchecked:=runtime.unchecked,noGc:=runtime.noGc,fixed:=runtime.fixed,
    thread:=thread,active:=active,release:=release,frameTracked:=by
      change frame.extra.borrowTracker = some (GeneralBorrowRawRootReleasePlan.frame release)
      rw [GeneralBorrowRawRootReleasePlan.frame,releaseId,releaseTag,releaseSlotId,releaseChild]
      exact fborrow,
    slotSize:=by rw [releaseSlot];exact slotSize,
    slotStorage:=by rw [releaseSlot];exact slotLen,
    slotMask:=by rw [releaseSlot];exact slotMask,
    slotProvenance:=by rw [releaseSlot];exact slotProv,
    slotMutable:=by rw [releaseSlot];exact slotMut,
    place:=s.place,layout:=s.layout,slotBase:=s.slotBase,slotPointer:=by rw [releaseSlotId,releaseRoot];exact s.slotPointer,aligned:=s.aligned,fits:=s.slotFits,
    cached:=by rw [releaseSlotId,runtime.addresses];exact s.slotCached,
    extras:=by rw [releaseSlotId];change machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [runtime.extras];exact s.extras,
    destination:=by rw [frp];rfl }
  exact ⟨input,rfl,rfl,rfl,rfl,releaseSlotId,rfl,call⟩

theorem invoke (s : Initial) :
    ∃ input : GeneralBorrowRawRootZeroPhysical.Input,
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧ input.release.slotId=s.slotId ∧ input.context=s.writeContext ∧
      Call.initStackFrame (ExecutionMachine.callHooks (config s.options (s.remaining+1) s.span) s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second 0)] false (.memory s.place) (.stop true) ⟨⟨#[]⟩,s.before⟩ =
        .ok () (Storage.withCurrent #[] input.before input.machine) ∧ GeneralBorrowRawRootZeroPhysical.Result input := by
  obtain ⟨input,options,limits,remaining,span,slotId,context,call⟩ := prepare s
  exact ⟨input,options,limits,remaining,span,slotId,context,call,GeneralBorrowRawRootZeroPhysical.complete input⟩

end
end DuplicatePrefix.GeneralBorrowRawRootZeroDescribed
