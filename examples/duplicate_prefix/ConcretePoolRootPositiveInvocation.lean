import duplicate_prefix.ConcretePoolRootInvocationEntry
import duplicate_prefix.RootZeroInvocationState
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.ConcretePoolRootInvocationState
import duplicate_prefix.WildcardHitRootRelease
import duplicate_prefix.EmptyForestPoolRejectedAfterLen
import duplicate_prefix.EmptyForestPoolSafetyToLen
import duplicate_prefix.ConcreteEmptyPoolContinuationData
import duplicate_prefix.PushThread
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true
set_option backward.dsimp.instances true
namespace DuplicatePrefix.ConcretePoolRootPositiveInvocation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver PhysicalMachineWrite
/-- Genuine positive-count live concrete empty-reference invocation, through actual
protected entry, physical false return, protector release, terminal ROOT return
and NoUBBeforeReturn. Resource and vacant-permission data remain explicit. -/
theorem invoke
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset count : UInt64) (nonzero : base+offset ≠ 0) (countNonzero : count ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (sharedTag lenTag : BorTag)
    (history : ConcreteEmptyPoolContinuationData.Input entry.allocation.extra parentTag tracker.global.nextPointerTag sharedTag lenTag)
    (race : before.dataRace = none)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (slotId : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slotBase : UInt64) (slotRoot : BorTag)
    (slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase))
    (aligned : place.mplace.misaligned = none)
    (slotCached : before.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩)
    (slotTree : slotEntry.allocation.extra = BorrowTree.new slotRoot (Size.ofBytes 1))
    (slotSize : slotEntry.allocation.byteSize = Size.ofBytes 1)
    (slotPresent : before.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry))
    (separate : slotId ≠ id)
    (slotFresh : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value < 18446744073709551615)
    (slotDistinct : slotRoot ≠ TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh)
    (slotParentDistinct : slotRoot ≠ tracker.global.nextPointerTag)
    (slotFree : tracker.global.protectedTags.contains slotRoot = false)
    (mutable : slotEntry.allocation.mutability = .Mut)
    (storage : slotEntry.allocation.len = slotEntry.allocation.byteSize.bytes.toNat)
    (maskLength : slotEntry.allocation.initializationMask.len = slotEntry.allocation.byteSize)
    (provenance : slotEntry.allocation.provenanceMap = ProvenanceMap.new)
    (noBackend : before.user.payload.payload.user.backend = .none)
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩))
    (thread : Miri.Concurrency.ThreadRecord)
    (active : before.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (source : PreparedContracts.SourceComparator) (mode : tracker.retagMode = .Default)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).gcInterval = 0)
    (fixed : before.threads.fixedScheduling = true) (fits : slotBase.toNat+1<2^64)
    (thirdFresh : (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615)
    (fourthFresh : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag.value < 18446744073709551615)
    (thirdTag : (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag = sharedTag)
    (fourthTag : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag = lenTag)
    (slotChildNotLen : (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag ≠ lenTag)
    (slotRootNotLen : slotRoot ≠ lenTag)
    (budget : Nat) (dispatchFuel : limits.callDispatch = budget+1) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let contextSafety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
      ⟨config,limits,fun _ _ => True⟩
    ∃ installed done,
      Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance
        RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
          (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace config limits installed done ∧
      ExecutionMachine.step config limits () done = (done,.ok false) ∧
      done.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn contextSafety 1 installed := by
  dsimp only
  let entryInput := history.entry
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span precise implicitWrites
  obtain ⟨retagCtx⟩ := ActualRetagContext.exists_context options (remaining+1) span precise implicitWrites
  obtain ⟨slotAllocation,call,protectedTree,protectedSize,protectedLen,protectedMask,protectedProv,protectedBytes,protectedMutable⟩ :=
    ConcretePoolRootInvocationEntry.enters options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id parentTag tracker base offset count nonzero entry before ghost shallow cachedAddress present enabled fresh entryInput race metadata notConstructed retagCtx place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize
      slotPresent separate slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache
  let raw := RawRootInvocation.root before place race
  let rawMachine := RawRootInvocation.machine #[] before
  let adjusted := (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm
  let tag := (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag
  let heldTracker := PositiveRootInvocationState.held tracker fresh slotFresh
  let frame := PositiveRootInstalledFrame.installed raw adjusted count {} id tracker.global.nextPointerTag slotId tag
  let initialMachine := ConcretePoolRootInvocationState.enteredMachine rawMachine tracker fresh id entry parentTag entryInput slotFresh slotId slotEntry slotRoot slotAllocation
  have call' : Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance
      RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
          (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame initialMachine) := by
    let arguments := RootArgumentsTwo.result
      (ConcreteEmptyRootArguments.firstDone raw adjusted {} id tracker.global.nextPointerTag) count
    let owned := ({} : FrameState).addProtector id tracker.global.nextPointerTag
    let changed := {arguments.frame with location := FrameLocation.unwinding ⟨601⟩}
    let actualFrame := CallEntryFacts.doneRootFrame
      {registeredFrame changed owned slotId tag with location := .unwinding ⟨559⟩}
    have frameEq : actualFrame = frame := rfl
    have machineEq := ConcretePoolRootInvocationState.entered_eq rawMachine tracker fresh id entry parentTag entryInput
      slotFresh slotId slotEntry slotRoot slotAllocation changed owned
    have stateEq := (congrArg (Storage.withCurrent #[] actualFrame) machineEq).trans
      (congrArg (fun f => Storage.withCurrent #[] f initialMachine) frameEq)
    exact call.trans (congrArg (EStateM.Result.ok ()) stateEq)
  obtain ⟨frameBody,frameIdentity,frameCallee,frameContinuation,frameReturn,frameVa,frameRace,frameBorrow,frameLocation⟩ :=
    PositiveRootInstalledFrame.metadata raw adjusted count {} id tracker.global.nextPointerTag slotId tag
  have frameSize : frame.locals.size=25 := PositiveRootInstalledFrame.size raw adjusted count {} id tracker.global.nextPointerTag slotId tag
  have valid0 : (0:MIR.LocalId)<frame.locals.size := by rw [frameSize];decide
  have slot0 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨0,by decide⟩
  have slot2 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨2,by decide⟩
  have slot3 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨3,by decide⟩
  have slot4 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨4,by decide⟩
  have slot5 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨5,by decide⟩
  simp only [Nat.reduceEqDiff,or_true,or_false,ite_true,ite_false] at slot0 slot2 slot3 slot4 slot5
  have allImmediate := PositiveRootInstalledFrame.immediate raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag
  have slot1 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨1,by decide⟩
  have slot13 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨13,by decide⟩
  simp only [Nat.reduceEqDiff,or_true,or_false,ite_true,ite_false] at slot1 slot13
  have unused : ∀j(v:j<frame.locals.size),7≤j→j≤12→(frame.locals[j]'v)=⟨.dead,none⟩ := by
    intro j v low high
    have bound : j<25 := by omega
    have known := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨j,bound⟩
    have not1 : j≠1 := by omega
    have not2 : j≠2 := by omega
    have not0 : j≠0 := by omega
    have not6 : j≠6 := by omega
    have not13 : j≠13 := by omega
    have not14 : j≠14 := by omega
    simpa only [Ne.symm not1,Ne.symm not2,Ne.symm not0,Ne.symm not6,Ne.symm not13,Ne.symm not14,Fin.val_mk,Bool.false_eq_true,ite_false,or_self] using known
  let bufferEntry2 : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := (entry.allocation.setExtra
    entryInput.after)}
  let input1 := history.first
  have bufferPresent2 : initialMachine.memory.live.find? (fun row => row.1 == id) = some (id,bufferEntry2) :=
    ConcretePoolRootInvocationState.buffer_lookup rawMachine tracker fresh id entry parentTag entryInput slotFresh slotId slotEntry slotRoot slotAllocation (Ne.symm separate)
  have slotPresent2 : initialMachine.memory.live.find? (fun row => row.1 == slotId) = some (slotId,{slotEntry with allocation := slotAllocation}) :=
    MemoryCopyBridge.live_lookup_replaced _ slotId _
  have rawFacts := RawRootInvocation.preservation #[] before
  have initialGhost : initialMachine.user.payload.ghost = false := rawFacts.2.2.2.2.1.trans ghost
  have initialShallow : initialMachine.user.payload.validation = .Shallow := rawFacts.2.2.2.2.2.1.trans shallow
  have uncheckedEntered : (config.terminators.getControl initialMachine.user).checkedArithmetic = false := by
    change (config.terminators.getControl rawMachine.user).checkedArithmetic = false
    rw [RootZeroInvocationState.raw_control]
    exact unchecked
  have noGcEntered : (config.terminators.getControl initialMachine.user).gcInterval = 0 := by
    change (config.terminators.getControl rawMachine.user).gcInterval = 0
    rw [RootZeroInvocationState.raw_control]
    exact noGc
  have initialAddr : initialMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    change rawMachine.user.addresses.baseAddr.find? _ = _
    rw [rawFacts.2.2.2.1]
    exact cachedAddress
  have baseEq : (ActualReferenceContext.config options remaining span).access.runtime.base =
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base := by
    rw [CanonicalConfigFacts.actual_access_runtime options () remaining span,CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span]
  have adjustedEq : adjusted = (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm := by
    dsimp only [adjusted]
    rw [baseEq]
  have initialSource1 : (frame.locals[1]'(by rw [frameSize];decide)).value = .live (.immediate adjusted) := congrArg (fun row => row.value) slot1
  obtain ⟨caller,prefixTrace,cb,ci,cf,ce,crp,crc,cva,cli,csz,cloc,c0,c1,c2,c7,c8,c9,c10,c11,c12,c13,ca⟩ :=
    EmptyForestPoolSafetyToLen.executes options limits remaining span source cmp precise implicitWrites debugOff dynamicFuel validityFuel fuelEq validationEq
      frame initialMachine tracker.global.nextPointerTag sharedTag id bufferEntry2 base offset count (by simpa using nonzero) countNonzero input1 frameSize
      (by simpa only [UInt64.add_zero] using (initialSource1.trans (congrArg (fun value => LocalValue.live (.immediate value)) adjustedEq))) (congrArg (fun row=>row.layout) slot1)
      (congrArg (fun row=>row.value) slot2) (congrArg (fun row=>row.layout) slot2)
      (congrArg (fun row=>row.value) slot3) (congrArg (fun row=>row.layout) slot3)
      (congrArg (fun row=>row.value) slot4) (congrArg (fun row=>row.value) slot5)
      (congrArg (fun row=>row.layout) slot4) (congrArg (fun row=>row.layout) slot5) unused
      (frameBody.trans raw.body) (frameIdentity.trans raw.identity) (frameCallee.trans raw.callee) frameLocation
      (frameRace.trans raw.noClocks) allImmediate heldTracker rfl mode thirdTag thirdFresh initialAddr bufferPresent2
      initialGhost initialShallow uncheckedEntered noGcEntered fixed
      (rawFacts.2.2.2.2.2.2.1 ▸ metadata) (rawFacts.2.2.2.2.2.2.1 ▸ notConstructed)
  let refTracker := ReferenceBorrowDriver.allocatedTracker heldTracker thirdFresh
  let tree3 := input1.after
  let afterRef := {ReferenceBorrowDriver.allocatedMachine (RootZeroCompleteState.tick options remaining span initialMachine) heldTracker thirdFresh with
    memory := RetagEntry.updatedMemory initialMachine.memory id bufferEntry2 tree3}
  let bufferEntry3 : LocalAllocation Provenance BorrowTree MiriMemoryKind := {bufferEntry2 with allocation := bufferEntry2.allocation.setExtra tree3}
  have callerValid (i : Fin 25) : i.val < caller.locals.size := by rw [csz];exact i.isLt
  have cpSlot (i : Fin 25) {row : LocalState Provenance LocalLayout} (known : caller.locals[i.val]? = some row) : caller.locals[i.val]'(callerValid i) = row :=
    Option.some.inj ((Array.getElem?_eq_getElem (callerValid i)).symm.trans known)
  have caller11 := cpSlot ⟨11,by decide⟩ c11
  have caller12 := cpSlot ⟨12,by decide⟩ c12
  have caller0 : caller.locals[0]'(callerValid ⟨0,by decide⟩) = ⟨.live (.immediate .uninit),none⟩ :=
    cpSlot ⟨0,by decide⟩ (c0.trans ((Array.getElem?_eq_getElem valid0).trans (congrArg some slot0)))
  have caller13 : caller.locals[13]'(callerValid ⟨13,by decide⟩) = ⟨.live (.immediate .uninit),none⟩ :=
    cpSlot ⟨13,by decide⟩ (c13.trans ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).trans (congrArg some slot13)))
  have rawActive : rawMachine.threads.activeThread? = some {thread with topUserRelevantFrame := some 0} := PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 thread 0 active
  have refActive : afterRef.threads.activeThread? = some {thread with topUserRelevantFrame := some 0} := rawActive
  have refTypes : afterRef.user.payload.payload.user.types = before.user.payload.payload.user.types := by
    change (RootZeroCompleteState.tick options remaining span initialMachine).user.payload.payload.user.types = _
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact rawFacts.2.2.2.2.2.2.1
  have refGhost : afterRef.user.payload.ghost = false := (RootZeroCompleteState.tick_ghost options remaining span initialMachine).trans initialGhost
  have refShallow : afterRef.user.payload.validation = .Shallow := (RootZeroCompleteState.tick_shallow options remaining span initialMachine).trans initialShallow
  have refUnchecked : (config.terminators.getControl afterRef.user).checkedArithmetic = false := (RootZeroCompleteState.tick_flags options remaining span initialMachine).1.trans uncheckedEntered
  have refGc : (config.terminators.getControl afterRef.user).gcInterval = 0 := (RootZeroCompleteState.tick_flags options remaining span initialMachine).2.trans noGcEntered
  have refBackend : afterRef.user.payload.payload.user.backend = .none := by
    change (RootZeroCompleteState.tick options remaining span initialMachine).user.payload.payload.user.backend = _
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1]
    exact rawFacts.2.2.2.2.2.2.2.1.trans noBackend
  have refAddr : afterRef.user.addresses = before.user.addresses := by
    change (RootZeroCompleteState.tick options remaining span initialMachine).user.addresses = _
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1]
    exact rawFacts.2.2.2.1
  have refPresent : afterRef.memory.live.find? (fun row => row.1 == id) = some (id,bufferEntry3) := MemoryCopyBridge.live_lookup_replaced _ id _
  have slotPresent3 : afterRef.memory.live.find? (fun row => row.1 == slotId) = some (slotId,{slotEntry with allocation := slotAllocation}) :=
    StackPopRelease.lookup_commit_other initialMachine.memory id slotId bufferEntry2 _ tree3 separate slotPresent2
  have slotFree3 : refTracker.global.protectedTags.contains slotRoot = false :=
    PositiveRootInvocationState.buffer_root_free tracker fresh slotFresh slotRoot slotParentDistinct slotDistinct slotFree
  have slotHeld3 : refTracker.global.protectedTags.contains tag = true := by
    change ((tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).insert tag .StrongProtector).contains tag = true
    simp [ProtectedTags.contains]
  let input2 := history.second
  let rootData := history.root
  have bf : caller.extra.borrowTracker = some ((({} : FrameState).addProtector id tracker.global.nextPointerTag).addProtector slotId tag) := by rw [ce,frameBorrow]
  have slotMaskValid : InitMaskCopy.WellFormed slotAllocation.initializationMask := by rw [protectedMask];trivial
  have rejected : count > (0:UInt64)/2 := by
    simpa only [UInt64.zero_div] using (UInt64.pos_iff_ne_zero.mpr countNonzero)
  obtain ⟨done,tail,terminal,empty,safe⟩ := EmptyForestPoolRejectedAfterLen.complete options limits remaining budget dispatchFuel span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    tracker.global.nextPointerTag sharedTag lenTag id bufferEntry3 base offset input2 rootData.index rootData.node rootData.tagged rootData.present rootData.unexposed rootData.absent
    (by simpa using nonzero) caller afterRef refTracker rfl fourthTag mode fourthFresh
    (callerValid ⟨11,by decide⟩) (by rw [caller11]) (by rw [caller11]) (by rw [ce,frameRace];exact raw.noClocks)
    refGhost refShallow (by rw [refAddr];exact cachedAddress) refPresent race
    {thread with topUserRelevantFrame := some 0} refActive rfl (refTypes ▸ metadata) (refTypes ▸ notConstructed)
    (cb.trans (frameBody.trans raw.body)) (ci.trans (frameIdentity.trans raw.identity)) (cf.trans (frameCallee.trans raw.callee)) cloc source
    (callerValid ⟨12,by decide⟩) (by rw [caller12]) (by rw [caller12]) refBackend refUnchecked refGc fixed
    count rejected csz ca (by rw [caller0]) (by rw [caller0]) (by rw [cpSlot ⟨7,by decide⟩ c7])
    (by rw [cpSlot ⟨8,by decide⟩ c8]) (by rw [cpSlot ⟨8,by decide⟩ c8])
    (by rw [cpSlot ⟨9,by decide⟩ c9]) (by rw [cpSlot ⟨9,by decide⟩ c9])
    (by rw [cpSlot ⟨10,by decide⟩ c10]) (by rw [cpSlot ⟨10,by decide⟩ c10])
    (by rw [caller13]) (by rw [caller13]) _ bf slotId {slotEntry with allocation := slotAllocation} slotRoot tag slotBase
    (by simp only [FrameState.addProtector];rfl) place layout slotPointer aligned (by rw [refAddr];exact slotCached) slotPresent3 separate
    protectedTree protectedSize protectedMutable (by rw [protectedLen,protectedSize];rfl) (by rw [protectedMask,protectedSize];rfl) slotMaskValid protectedProv
    (by change afterRef.user.payload.payload.user.runtime.extras.allocations.find? _ = _; change (RootZeroCompleteState.tick options remaining span initialMachine).user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2];exact rawFacts.2.2.2.2.2.2.2.2 ▸ extras)
    slotFree3 slotHeld3 slotDistinct slotRootNotLen slotChildNotLen (crc.trans (frameContinuation.trans (RawRootInvocation.control before place race).2.2.1))
    (by rw [crp,frameReturn];rfl) (by rw [cva,frameVa];rfl) fits
  have trace : SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame initialMachine) done := SuccessfulTrace.append prefixTrace tail
  refine ⟨Storage.withCurrent #[] frame initialMachine,done,call',trace,terminal,empty,?_⟩
  exact SuccessfulTrace.no_ub ⟨config,limits,fun _ _ => True⟩ 1 _ done (by exact ⟨by decide,rfl⟩) trace
    (by change done.stack.frames.size < 1;rw [empty];decide)

end DuplicatePrefix.ConcretePoolRootPositiveInvocation
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.ConcretePoolRootPositiveInvocation.invoke) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved whole wildcard HIT rejected invocation dependency {dependency}"
#print axioms DuplicatePrefix.ConcretePoolRootPositiveInvocation.invoke
