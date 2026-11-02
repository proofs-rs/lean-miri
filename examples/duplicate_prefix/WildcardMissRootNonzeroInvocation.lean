import duplicate_prefix.RootZeroInvocationState
import duplicate_prefix.WildcardMissRootInvocationEntry
import duplicate_prefix.WildcardMissRootSafetyToLen
import duplicate_prefix.EmptyRootSafetyExit
import duplicate_prefix.WildcardMissRootLenCall
import duplicate_prefix.WildcardMissRootInstalledFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.WildcardMissRootNonzeroInvocation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver PhysicalMachineWrite
theorem invoke
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : before.borrowTracker = some tracker)
    (initialFresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag initialFresh).value < 18446744073709551615)
    (thirdFresh : (RootZeroInvocationState.held tracker initialFresh fresh).global.nextPointerTag.value<18446744073709551615)
    (fourthFresh : (ReferenceBorrowDriver.allocatedTracker (RootZeroInvocationState.held tracker initialFresh fresh) thirdFresh).global.nextPointerTag.value<18446744073709551615)
    (budget : Nat) (dispatch : limits.callDispatch=budget+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base : UInt64) (rootTag : BorTag)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id rootTag)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (cached : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (root : entry.allocation.extra = BorrowTree.new rootTag (Size.ofBytes 1))
    (size : entry.allocation.byteSize = Size.ofBytes 1)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : before.dataRace = none)
    (distinct : rootTag ≠ TypedRetagEmpty.successorTag tracker.global.nextPointerTag initialFresh)
    (unprotected : tracker.global.protectedTags.contains rootTag = false)
    (mutable : entry.allocation.mutability = .Mut)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (provenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (noBackend : before.user.payload.payload.user.backend = .none)
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (ghost : before.user.payload.ghost = false)
    (target : TargetDataLayout)
    (targetEq : target = (ActualReferenceContext.config options remaining span).access.runtime.base)
    (address count : UInt64) (nonzero : address ≠ 0) (countNonzero : count≠0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel = dynamicFuel+1) (validityEq : options.limits.validation = validityFuel+1)
    (shallow : before.user.payload.validation = .Shallow)
    (addressMode : before.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardMissAddress.Miss before.user.addresses address)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord)
    (active : before.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none)
    (source : PreparedContracts.SourceComparator) (mode : tracker.retagMode=.Default)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).checkedArithmetic=false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).gcInterval=0)
    (fixed : before.threads.fixedScheduling=true)
    (fits : base.toNat+1<2^64) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let contextSafety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
      ⟨config,limits,fun _ _ => True⟩
    ∃ installed done,
      Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance
        RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (WildcardMissRootArguments.first target address),.Copy (WildcardMissRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace config limits installed done ∧
      ExecutionMachine.step config limits () done = (done,.ok false) ∧
      CallSafety.NoUBBeforeReturn contextSafety 1 installed := by
  dsimp only
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  obtain ⟨ctx⟩ := ActualRetagContext.exists_context options (remaining+1) span precise implicitWrites
  obtain ⟨slotAllocation,call,protectedTree,protectedSize,protectedLen,protectedMask,protectedProv,protectedBytes,protectedMutable⟩ :=
    WildcardMissRootInvocationEntry.enters options limits remaining span ctx place layout before tracker enabled initialFresh fresh
      id entry base rootTag pointer aligned cached root size present race distinct unprotected mutable storage maskLength provenance
      noBackend extras ghost target targetEq address count nonzero cmp precise implicitWrites debug dynamicFuel validityFuel dynamicEq validityEq shallow addressMode miss metadata
      notConstructed thread active noCache
  let raw := RawRootInvocation.root before place race
  let rawMachine := RawRootInvocation.machine #[] before
  let tag := RootZeroInvocationState.child tracker initialFresh
  let heldTracker := RootZeroInvocationState.held tracker initialFresh fresh
  let frame := WildcardMissRootInstalledFrame.installed raw target address count {} id tag
  let initialMachine := RootZeroInvocationState.enteredMachine rawMachine tracker initialFresh fresh id entry rootTag slotAllocation
  have call' : Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance
      RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (WildcardMissRootArguments.first target address),.Copy (WildcardMissRootArguments.second count)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame initialMachine) := by
    rw [RootZeroInvocationState.entered_eq] at call
    exact call
  obtain ⟨frameBody,frameIdentity,frameCallee,frameContinuation,frameReturn,frameVa,frameRace,frameBorrow,frameLocation⟩ :=
    WildcardMissRootInstalledFrame.metadata raw target address count {} id tag
  have frameSize : frame.locals.size=25 := WildcardMissRootInstalledFrame.size raw target address count {} id tag
  have valid0 : (0:MIR.LocalId)<frame.locals.size := by rw [frameSize];decide
  have slot0 := WildcardMissRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) target address count {} id tag ⟨0,by decide⟩
  have slot2 := WildcardMissRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) target address count {} id tag ⟨2,by decide⟩
  have slot3 := WildcardMissRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) target address count {} id tag ⟨3,by decide⟩
  have slot4 := WildcardMissRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) target address count {} id tag ⟨4,by decide⟩
  have slot5 := WildcardMissRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) target address count {} id tag ⟨5,by decide⟩
  simp only [Fin.val_mk,eq_self_iff_true,Nat.reduceEqDiff,or_true,or_false,true_or,false_or,ite_true,ite_false] at slot0 slot2 slot3 slot4 slot5
  have allImmediate := WildcardMissRootInstalledFrame.immediate raw (RawRootInvocation.locals before place race) target address count {} id tag
  have slot1 := WildcardMissRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) target address count {} id tag ⟨1,by decide⟩
  have slot13 := WildcardMissRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) target address count {} id tag ⟨13,by decide⟩
  simp only [Fin.val_mk,eq_self_iff_true,Nat.reduceEqDiff,or_true,or_false,true_or,false_or,ite_true,ite_false] at slot1 slot13
  have unused : ∀j(v:j<frame.locals.size),7≤j→j≤12→(frame.locals[j]'v)=⟨.dead,none⟩ := by
    intro j v low high
    have bound : j<25 := by omega
    have known := WildcardMissRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) target address count {} id tag ⟨j,bound⟩
    have not1 : j≠1 := by omega
    have not2 : j≠2 := by omega
    have not0 : j≠0 := by omega
    have not6 : j≠6 := by omega
    have not13 : j≠13 := by omega
    have not14 : j≠14 := by omega
    simpa only [Ne.symm not1,Ne.symm not2,Ne.symm not0,Ne.symm not6,Ne.symm not13,Ne.symm not14,Fin.val_mk,Bool.false_eq_true,ite_false,or_self] using known
  have rawFacts := RawRootInvocation.preservation #[] before
  have initialGhost : initialMachine.user.payload.ghost=false := rawFacts.2.2.2.2.1.trans ghost
  have initialShallow : initialMachine.user.payload.validation=.Shallow := rawFacts.2.2.2.2.2.1.trans shallow
  have uncheckedEntered : (config.terminators.getControl initialMachine.user).checkedArithmetic=false := by
    change (config.terminators.getControl rawMachine.user).checkedArithmetic=false
    rw [RootZeroInvocationState.raw_control]
    exact unchecked
  have noGcEntered : (config.terminators.getControl initialMachine.user).gcInterval=0 := by
    change (config.terminators.getControl rawMachine.user).gcInterval=0
    rw [RootZeroInvocationState.raw_control]
    exact noGc
  have targetOuter : target=(PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base := by
    rw [targetEq]
    rw [CanonicalConfigFacts.actual_access_runtime options () remaining span,
      CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span]
  have initialMode : initialMachine.user.addresses.provenanceMode ≠ .strict := by
    change rawMachine.user.addresses.provenanceMode ≠ .strict
    rw [rawFacts.2.2.2.1];exact addressMode
  have initialBelow : WildcardMissAddress.Miss initialMachine.user.addresses address := by
    change WildcardMissAddress.Miss rawMachine.user.addresses address
    rw [rawFacts.2.2.2.1];exact miss
  obtain ⟨caller,prefixTrace,cb,ci,cf,ce,crp,crc,cva,cli,csz,cloc,c0,c1,c2,c7,c8,c9,c10,c11,c12,c13,ca⟩ :=
    WildcardMissRootSafetyToLen.executes options limits remaining span source cmp precise implicitWrites debug dynamicFuel validityFuel dynamicEq validityEq
      frame initialMachine address count nonzero countNonzero frameSize
      (by rw [←targetOuter];exact congrArg (fun row=>row.value) slot1) (congrArg (fun row=>row.layout) slot1)
      (congrArg (fun row=>row.value) slot2) (congrArg (fun row=>row.layout) slot2)
      (congrArg (fun row=>row.value) slot3) (congrArg (fun row=>row.layout) slot3)
      (congrArg (fun row=>row.value) slot4) (congrArg (fun row=>row.value) slot5)
      (congrArg (fun row=>row.layout) slot4) (congrArg (fun row=>row.layout) slot5) unused
      (frameBody.trans raw.body) (frameIdentity.trans raw.identity) (frameCallee.trans raw.callee) frameLocation
      (frameRace.trans raw.noClocks) allImmediate heldTracker rfl mode thirdFresh initialGhost initialShallow uncheckedEntered noGcEntered fixed
      initialMode initialBelow (rawFacts.2.2.2.2.2.2.1 ▸ metadata) (rawFacts.2.2.2.2.2.2.1 ▸ notConstructed)
  let afterRef := ReferenceBorrowDriver.allocatedMachine (RootZeroCompleteState.tick options remaining span initialMachine) heldTracker thirdFresh
  let refTracker := ReferenceBorrowDriver.allocatedTracker heldTracker thirdFresh
  have vcaller (i : Fin 25) : i.val<caller.locals.size := by rw [csz];exact i.isLt
  have caller11 : (caller.locals[11]'(vcaller ⟨11,by decide⟩))=⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vcaller ⟨11,by decide⟩)).symm.trans c11)
  have caller12 : (caller.locals[12]'(vcaller ⟨12,by decide⟩))=⟨.live (.immediate (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm),some SharedReferenceMetadata.sharedLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (vcaller ⟨12,by decide⟩)).symm.trans c12)
  have rawActive : rawMachine.threads.activeThread?=some {thread with topUserRelevantFrame:=some 0} :=
    PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 thread 0 active
  have refActive : afterRef.threads.activeThread?=some {thread with topUserRelevantFrame:=some 0} := rawActive
  have refTypes : afterRef.user.payload.payload.user.types=before.user.payload.payload.user.types := by
    change (RootZeroCompleteState.tick options remaining span initialMachine).user.payload.payload.user.types=before.user.payload.payload.user.types
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact rawFacts.2.2.2.2.2.2.1
  have refGhost : afterRef.user.payload.ghost=false := (RootZeroCompleteState.tick_ghost options remaining span initialMachine).trans initialGhost
  have refShallow : afterRef.user.payload.validation=.Shallow := (RootZeroCompleteState.tick_shallow options remaining span initialMachine).trans initialShallow
  have refUnchecked : (config.terminators.getControl afterRef.user).checkedArithmetic=false :=
    (RootZeroCompleteState.tick_flags options remaining span initialMachine).1.trans uncheckedEntered
  have refGc : (config.terminators.getControl afterRef.user).gcInterval=0 :=
    (RootZeroCompleteState.tick_flags options remaining span initialMachine).2.trans noGcEntered
  obtain ⟨referenceContext⟩ := ActualReferenceContext.exists_context options remaining span precise implicitWrites
  have refBackend : afterRef.user.payload.payload.user.backend=.none := by
    change (RootZeroCompleteState.tick options remaining span initialMachine).user.payload.payload.user.backend=.none
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1]
    exact rawFacts.2.2.2.2.2.2.2.1.trans noBackend
  have refAddresses : afterRef.user.addresses=before.user.addresses := by
    change (RootZeroCompleteState.tick options remaining span initialMachine).user.addresses=before.user.addresses
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1]
    exact rawFacts.2.2.2.1
  have refMode : afterRef.user.addresses.provenanceMode ≠ .strict := by rw [refAddresses];exact addressMode
  have refBelow : WildcardMissAddress.Miss afterRef.user.addresses address := by rw [refAddresses];exact miss
  obtain ⟨lenMachine,lenTrace,lenMemory,lenBorrow,lenGhost,lenShallow,lenRace,lenFixed,lenUnchecked,lenGc,lenAddresses,lenTypes,lenBackend,lenExtras,lenThread,lenActive⟩ :=
    WildcardMissRootLenCall.returns_zero options limits remaining budget dispatch span referenceContext debug cmp dynamicFuel validityFuel dynamicEq validityEq
      address nonzero caller afterRef refTracker rfl mode fourthFresh (vcaller ⟨11,by decide⟩)
      (by rw [caller11]) (by rw [caller11]) (by rw [ce,frameRace];exact raw.noClocks) refGhost refShallow race
      {thread with topUserRelevantFrame:=some 0} refActive rfl refMode refBelow (refTypes ▸ metadata) (refTypes ▸ notConstructed)
      (cb.trans (frameBody.trans raw.body)) (ci.trans (frameIdentity.trans raw.identity)) (cf.trans (frameCallee.trans raw.callee)) cloc source
      (vcaller ⟨12,by decide⟩) (by rw [caller12]) (by rw [caller12]) refBackend refUnchecked refGc fixed
  let endFrame := LenCallResultFrame.resultFrame caller (vcaller ⟨11,by decide⟩) 0
  let endTracker := ReferenceBorrowDriver.allocatedTracker refTracker fourthFresh
  have endSize : endFrame.locals.size=25 := (LenCallResultFrame.size caller _ 0).trans csz
  have endValid (i : Fin 25) : i.val<endFrame.locals.size := by rw [endSize];exact i.isLt
  have endSlot (n : Fin 25) (different : n.val≠11) :
      (endFrame.locals[n.val]'(endValid n))=(caller.locals[n.val]'(vcaller n)) :=
    Option.some.inj ((Array.getElem?_eq_getElem (endValid n)).symm.trans
      ((LenCallResultFrame.other caller _ 0 n.val different).trans (Array.getElem?_eq_getElem (vcaller n))))
  have end0 : (endFrame.locals[0]'(endValid ⟨0,by decide⟩))=⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (endValid ⟨0,by decide⟩)).symm.trans
      ((LenCallResultFrame.other caller _ 0 0 (by decide)).trans (c0.trans ((Array.getElem?_eq_getElem valid0).trans (congrArg some slot0)))))
  have end13 : (endFrame.locals[13]'(endValid ⟨13,by decide⟩))=⟨.live (.immediate .uninit),none⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (endValid ⟨13,by decide⟩)).symm.trans
      ((LenCallResultFrame.other caller _ 0 13 (by decide)).trans (c13.trans ((Array.getElem?_eq_getElem (by rw [frameSize];decide)).trans (congrArg some slot13)))))
  have end11 : (endFrame.locals[11]'(endValid ⟨11,by decide⟩))=⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem (endValid ⟨11,by decide⟩)).symm.trans (LenCallResultFrame.value caller _ 0))
  have cpSlot (n : Fin 25) {row : LocalState Provenance LocalLayout} (known : caller.locals[n.val]?=some row) : (caller.locals[n.val]'(vcaller n))=row :=
    Option.some.inj ((Array.getElem?_eq_getElem (vcaller n)).symm.trans known)
  have end7 := (endSlot ⟨7,by decide⟩ (by decide)).trans (cpSlot ⟨7,by decide⟩ c7)
  have end8 := (endSlot ⟨8,by decide⟩ (by decide)).trans (cpSlot ⟨8,by decide⟩ c8)
  have end9 := (endSlot ⟨9,by decide⟩ (by decide)).trans (cpSlot ⟨9,by decide⟩ c9)
  have end10 := (endSlot ⟨10,by decide⟩ (by decide)).trans (cpSlot ⟨10,by decide⟩ c10)
  have end12 := (endSlot ⟨12,by decide⟩ (by decide)).trans caller12
  have endAll := LenCallResultFrame.all_immediate caller (vcaller ⟨11,by decide⟩) 0 ca
  let bM := RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span lenMachine)))
  let newEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation:=slotAllocation}
  let bf : FrameState := ({} : FrameState).addProtector id tag
  let releasedMemory := StackPopRelease.commitTree bM.memory id newEntry slotAllocation.extra
  let postTracker := {endTracker with global:=endTracker.global.endCall bf}
  let popped := GenericPopFrame.afterRelevanceAt #[] endFrame (ActualPopPlan.released bM releasedMemory endTracker bf) (lenThread.topUserRelevantFrame.getD 0)
  let state : MachineHooks.State MiriMemoryKind Machine.RootUser := ⟨⟨#[]⟩,popped⟩
  have heldFree := RootZeroInvocationState.held_root_free tracker initialFresh fresh rootTag distinct unprotected
  have heldChild := RootZeroInvocationState.held_child tracker initialFresh fresh
  have initialPresent : lenMachine.memory.live.find? (fun row => row.1 == id)=some (id,newEntry) := by
    rw [lenMemory]
    exact RootZeroInvocationState.entered_lookup rawMachine tracker initialFresh fresh id entry rootTag slotAllocation
  have profile : RootPhysicalReturnPlan.Profile endTracker.global.protectedTags bf.protectedTags.toList bM.memory releasedMemory := by
    apply RootPhysicalReturnPlan.Profile.slot id rootTag tag 1 true newEntry [] bM.memory releasedMemory
      initialPresent protectedTree heldFree heldChild distinct (by decide)
    exact .nil _
  have activeEntered : bM.threads.activeThread?=some lenThread := lenActive
  have stateUser : state.machine.user=bM.user := by
    dsimp only [state,popped,GenericPopFrame.afterRelevanceAt]
    split <;> rfl
  have stateRace : state.machine.dataRace=none := by
    dsimp only [state,popped,GenericPopFrame.afterRelevanceAt]
    split <;> exact lenRace
  have stateBorrow : state.machine.borrowTracker=some postTracker := by
    dsimp only [state,popped,GenericPopFrame.afterRelevanceAt]
    split <;> rfl
  have addrState : state.machine.user.addresses=before.user.addresses := by
    rw [stateUser]
    change bM.user.addresses=before.user.addresses
    dsimp only [bM]
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1,lenAddresses]
    change (RootZeroCompleteState.tick options remaining span initialMachine).user.addresses=before.user.addresses
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1]
    exact rawFacts.2.2.2.1
  have backendState : state.machine.user.payload.payload.user.backend=.none := by
    rw [stateUser]
    change bM.user.payload.payload.user.backend=.none
    dsimp only [bM]
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1,lenBackend]
    change (RootZeroCompleteState.tick options remaining span initialMachine).user.payload.payload.user.backend=.none
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1]
    exact rawFacts.2.2.2.2.2.2.2.1.trans noBackend
  have extrasState : state.machine.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras := by
    rw [stateUser]
    change bM.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras
    dsimp only [bM]
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2,lenExtras]
    change (RootZeroCompleteState.tick options remaining span initialMachine).user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2]
    exact rawFacts.2.2.2.2.2.2.2.2
  have ghostState : state.machine.user.payload.ghost=false := by
    rw [stateUser]
    change bM.user.payload.ghost=false
    dsimp only [bM]
    rw [RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost]
    exact lenGhost
  have shallowState : state.machine.user.payload.validation=.Shallow := by
    rw [stateUser]
    change bM.user.payload.validation=.Shallow
    dsimp only [bM]
    rw [RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow]
    exact lenShallow
  have rootFree : postTracker.global.protectedTags.contains rootTag=false := by
    rw [StackPopRelease.end_call_contains]
    split
    · rfl
    · exact heldFree
  have childFree : postTracker.global.protectedTags.contains tag=false := by
    rw [StackPopRelease.end_call_contains]
    simp [bf,FrameState.addProtector]
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have innerFields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨outer,outerAccess,outerArithmetic,_⟩ := fields.canonicalCopy
  obtain ⟨inner,innerAccess,innerArithmetic,_⟩ := innerFields.canonicalCopy
  have outerWidth : outer.pointers.arithmetic=⟨Size.ofBytes 8⟩ := outerArithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () (remaining+1) span)
  have innerWidth : inner.pointers.arithmetic=⟨Size.ofBytes 8⟩ := innerArithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () remaining span)
  have outerRuntime : outer.access.runtime=PreparedReflection.actual.runtime.target :=
    (congrArg (fun access => access.runtime) outerAccess).symm.trans (CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span)
  have innerRuntime : inner.access.runtime=PreparedReflection.actual.runtime.target :=
    (congrArg (fun access => access.runtime) innerAccess).symm.trans (CanonicalConfigFacts.actual_access_runtime options () remaining span)
  have endpoint : (allocRange place.mplace.ptr.offset (Size.ofBytes 1)).endExclusive=.ok (Size.ofBytes (base+1)) := by
    rw [pointer]
    have added := size_add_ok (Size.ofBytes base) (Size.ofBytes 1) (by simpa only [Size.ofBytes,UInt64.toNat_one] using fits)
    simp only [Pointer.new,allocRange,AllocRange.endExclusive,AllocRange.end,added,Except.mapError]
    rfl
  have maskValid : InitMaskCopy.WellFormed slotAllocation.initializationMask := by rw [protectedMask];trivial
  have endFrameBorrow : endFrame.extra.borrowTracker=some bf := by change caller.extra.borrowTracker=some bf;rw [ce];exact frameBorrow
  have endFrameBody : endFrame.body=RootBody.reflected.body.body := cb.trans (frameBody.trans raw.body)
  have endFrameIdentity : endFrame.bodyIdentity=RootBody.reflected.body.identity := ci.trans (frameIdentity.trans raw.identity)
  have endFrameCallee : endFrame.functionInstance=RootBody.reflected.functionInstance := cf.trans (frameCallee.trans raw.callee)
  obtain ⟨result,tailTrace,terminal,tailSafe,props⟩ := EmptyRootSafetyExit.complete outer inner options remaining span innerAccess innerWidth
    (by rw [innerRuntime];rfl) (by rw [innerRuntime,outerRuntime]) limits validityFuel debug validityEq
    endFrame lenMachine bM rfl lenUnchecked lenGc lenFixed endTracker bf (by exact lenBorrow) endFrameBorrow releasedMemory profile
    lenThread activeEntered state rfl endFrameBody endFrameIdentity endFrameCallee rfl endSize source count
    (UInt64.pos_iff_ne_zero.mpr countNonzero) (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm
    (by rw [end12]) (by rw [end13]) (by rw [end13])
    (by rw [end7]) (by rw [end8]) (by rw [end8]) (by rw [end9]) (by rw [end9])
    (by rw [end10]) (by rw [end10]) (by rw [end11]) (by rw [end11]) lenGhost lenShallow mode
    (endValid ⟨0,by decide⟩) (by change caller.extra.dataRace=none;rw [ce,frameRace];exact raw.noClocks)
    (crc.trans (frameContinuation.trans (RawRootInvocation.control before place race).2.2.1)) endAll
    (by change caller.vaList=#[];rw [cva,frameVa];rfl) place id rootTag tag true base 1 newEntry postTracker
    (by rw [end0]) (by rw [end0]) rfl layout outerWidth (by decide) (by decide)
    (by rw [addrState];exact cached) initialPresent protectedSize protectedMutable maskValid (by rw [outerRuntime];rfl)
    (by rw [protectedLen,protectedSize];rfl) (by rw [protectedMask,protectedSize];rfl) protectedProv stateRace backendState stateBorrow
    (by change state.machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [extrasState];exact extras)
    rootFree childFree protectedTree pointer aligned (by rw [outerRuntime];rfl) outerAccess ghostState shallowState
    (by change caller.returnPlace.toRuntimePlace=_;rw [crp,frameReturn];rfl) (Size.ofBytes (base+1)) endpoint
  have fullTrace := SuccessfulTrace.append prefixTrace (SuccessfulTrace.append lenTrace tailTrace)
  let done := CanonicalCopy.replaceAllocation state id entry.kind result
  have safe : CallSafety.NoUBBeforeReturn (⟨config,limits,fun _ _=>True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
      1 (Storage.withCurrent #[] frame initialMachine) :=
    SuccessfulTrace.no_ub _ 1 _ done (by simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]) fullTrace (by change (0:Nat)<1;decide)
  exact ⟨Storage.withCurrent #[] frame initialMachine,done,call',fullTrace,terminal,safe⟩

#print axioms invoke
end DuplicatePrefix.WildcardMissRootNonzeroInvocation
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.WildcardMissRootNonzeroInvocation.invoke) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved genuine nonzero empty invocation dependency {dependency}"
