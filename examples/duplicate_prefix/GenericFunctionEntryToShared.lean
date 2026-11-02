import duplicate_prefix.GenericFunctionEntryPrefix
import duplicate_prefix.GenericFunctionEntryState
import duplicate_prefix.PositiveRootInstalledFrame

namespace DuplicatePrefix.GenericFunctionEntryToShared
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

structure Ready (frame : CompilerFrameContext.ActualFrame) (value : Immediate Provenance)
    (count : UInt64) (borrowFrame : FrameState) : Prop where
  body : frame.body = RootBody.reflected.body.body
  identity : frame.bodyIdentity = RootBody.reflected.body.identity
  callee : frame.functionInstance = RootBody.reflected.functionInstance
  size : frame.locals.size = 25
  location : frame.location = .mir ⟨2,11⟩
  source : frame.locals[1]? = some ⟨.live (.immediate value),some ActualReferenceMetadata.reference⟩
  countSlot : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  lenSlot : frame.locals[11]? = some ⟨.live (.immediate .uninit),none⟩
  exprSlot : frame.locals[12]? = some ⟨.live (.immediate .uninit),none⟩
  noClocks : frame.extra.dataRace = none
  borrowed : frame.extra.borrowTracker = some borrowFrame
  immediate : CopyHelperCleanup.AllImmediate frame
  slot0 : frame.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  slot7 : frame.locals[7]? = some ⟨.live (.immediate .uninit),none⟩
  slot8 : frame.locals[8]? = some ⟨.live (.immediate .uninit),none⟩
  slot10 : frame.locals[10]? = some ⟨.live (.immediate .uninit),none⟩
  slot13 : frame.locals[13]? = some ⟨.live (.immediate .uninit),none⟩
  slot9 : frame.locals[9]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
  slot15 : frame.locals[15]? = some ⟨.dead,none⟩
  slot16 : frame.locals[16]? = some ⟨.dead,none⟩

theorem enters_shared_boundary
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset len count : UInt64) (nonzero : base+offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (data : GenericAsMutPtrEntryValidity.Data entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (race : before.dataRace = none)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (retagCtx : ActualRetagContext.Context options (remaining+1) span)
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
    (source : PreparedContracts.SourceComparator) (mode : tracker.retagMode = .Default)
    (countPositive : (0 : UInt64) < count)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).gcInterval = 0)
    (fixed : before.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let adjusted := (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let frame := PositiveRootInstalledFrame.installed (RawRootInvocation.root before place race) adjusted count {} id tracker.global.nextPointerTag
      slotId (GenericFunctionEntryState.next tracker fresh).global.nextPointerTag
    ∃ (slotAllocation : Allocation Provenance BorrowTree) (result : CompilerFrameContext.ActualFrame),
      let initialMachine := GenericFunctionEntryState.enteredMachine (RawRootInvocation.machine #[] before) tracker fresh id entry parentTag offset len
        slotFresh slotId slotEntry slotRoot slotAllocation
      Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
          (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
        .ok () (Storage.withCurrent #[] frame initialMachine) ∧
      SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame initialMachine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span initialMachine)) ∧
      GenericFunctionEntryPrefix.Shape frame result count ∧
      Ready result adjusted count ((({} : FrameState).addProtector id tracker.global.nextPointerTag).addProtector
        slotId (GenericFunctionEntryState.next tracker fresh).global.nextPointerTag) ∧
      slotAllocation.extra = PhysicalMachineWrite.slotTree slotRoot (GenericFunctionEntryState.next tracker fresh).global.nextPointerTag 1 true ∧
      slotAllocation.byteSize = Size.ofBytes 1 ∧ slotAllocation.len = 1 ∧
      slotAllocation.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      slotAllocation.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot slotAllocation = AllocationCopy.snapshot slotEntry.allocation ∧
      slotAllocation.mutability = .Mut := by
  dsimp only
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  obtain ⟨slotAllocation,call,protectedTree,protectedSize,protectedLen,protectedMask,protectedProv,protectedBytes,protectedMutable⟩ :=
    GenericFunctionEntryInvocation.enters options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id parentTag tracker base offset len count nonzero entry positive signedFits bounds before ghost shallow cachedAddress present enabled fresh
      data capacity race metadata notConstructed retagCtx place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize
      slotPresent separate slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache
  let raw := RawRootInvocation.root before place race
  let rawMachine := RawRootInvocation.machine #[] before
  let adjusted := (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let tag := (GenericFunctionEntryState.next tracker fresh).global.nextPointerTag
  let heldTracker := GenericFunctionEntryState.held tracker fresh slotFresh
  let frame := PositiveRootInstalledFrame.installed raw adjusted count {} id tracker.global.nextPointerTag slotId tag
  let initialMachine := GenericFunctionEntryState.enteredMachine rawMachine tracker fresh id entry parentTag offset len slotFresh slotId slotEntry slotRoot slotAllocation
  have call' : Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance
      RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
          (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame initialMachine) := by
    rw [GenericFunctionEntryState.entered_eq] at call
    exact call
  obtain ⟨frameBody,frameIdentity,frameCallee,frameContinuation,frameReturn,frameVa,frameRace,frameBorrow,frameLocation⟩ :=
    PositiveRootInstalledFrame.metadata raw adjusted count {} id tracker.global.nextPointerTag slotId tag
  have frameSize : frame.locals.size=25 := PositiveRootInstalledFrame.size raw adjusted count {} id tracker.global.nextPointerTag slotId tag
  have slot2 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨2,by decide⟩
  have slot3 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨3,by decide⟩
  have slot4 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨4,by decide⟩
  have slot5 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨5,by decide⟩
  simp only [Fin.val_mk,eq_self_iff_true,Nat.reduceEqDiff,or_true,or_false,true_or,false_or,ite_true,ite_false] at slot2 slot3 slot4 slot5
  have allImmediate := PositiveRootInstalledFrame.immediate raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag
  have slot1 := PositiveRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨1,by decide⟩
  simp only [Fin.val_mk,eq_self_iff_true,Nat.reduceEqDiff,or_true,or_false,true_or,false_or,ite_true,ite_false] at slot1
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
  have rawFacts := RawRootInvocation.preservation #[] before
  have initialGhost : initialMachine.user.payload.ghost = false := rawFacts.2.2.2.2.1.trans ghost
  have initialShallow : initialMachine.user.payload.validation = .Shallow := rawFacts.2.2.2.2.2.1.trans shallow
  have rawControl : config.terminators.getControl rawMachine.user = config.terminators.getControl before.user := by
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have uncheckedEntered : (config.terminators.getControl initialMachine.user).checkedArithmetic = false := by
    change (config.terminators.getControl rawMachine.user).checkedArithmetic = false
    rw [rawControl]
    exact unchecked
  have noGcEntered : (config.terminators.getControl initialMachine.user).gcInterval = 0 := by
    change (config.terminators.getControl rawMachine.user).gcInterval = 0
    rw [rawControl]
    exact noGc
  obtain ⟨result,trace,shape⟩ := GenericFunctionEntryPrefix.executes_preserving options limits remaining span source debugOff validityFuel validationEq
    frame initialMachine count (UInt64.pos_iff_ne_zero.mp countPositive) frameSize
    (congrArg (fun row => row.value) slot2) (congrArg (fun row => row.layout) slot2)
    (congrArg (fun row => row.value) slot3) (congrArg (fun row => row.layout) slot3)
    (congrArg (fun row => row.value) slot4) (congrArg (fun row => row.value) slot5)
    (congrArg (fun row => row.layout) slot4) (congrArg (fun row => row.layout) slot5) unused
    (frameBody.trans raw.body) (frameIdentity.trans raw.identity) (frameCallee.trans raw.callee) frameLocation
    (frameRace.trans raw.noClocks) allImmediate heldTracker rfl mode initialGhost initialShallow uncheckedEntered noGcEntered fixed
  have sourceOption : frame.locals[1]? = some ⟨.live (.immediate adjusted),some ActualReferenceMetadata.reference⟩ := by
    rw [Array.getElem?_eq_getElem (by rw [frameSize];decide : 1 < frame.locals.size)]
    exact congrArg some slot1
  have countOption : frame.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ := by
    rw [Array.getElem?_eq_getElem (by rw [frameSize];decide : 2 < frame.locals.size)]
    exact congrArg some slot2
  have original0 := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals before place race)
    adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨0,by decide⟩
  simp only [Fin.val_mk,Nat.reduceEqDiff,eq_self_iff_true,or_true,or_false,true_or,false_or,ite_true,ite_false] at original0
  have original13 := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals before place race)
    adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨13,by decide⟩
  simp only [Fin.val_mk,Nat.reduceEqDiff,eq_self_iff_true,or_true,or_false,true_or,false_or,ite_true,ite_false] at original13
  have original15 := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals before place race)
    adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨15,by decide⟩
  simp only [Fin.val_mk,Nat.reduceEqDiff,eq_self_iff_true,or_true,or_false,true_or,false_or,ite_true,ite_false] at original15
  have original16 := PositiveRootInstalledFrame.slot_option raw (RawRootInvocation.locals before place race)
    adjusted count {} id tracker.global.nextPointerTag slotId tag ⟨16,by decide⟩
  simp only [Fin.val_mk,Nat.reduceEqDiff,eq_self_iff_true,or_true,or_false,true_or,false_or,ite_true,ite_false] at original16
  refine ⟨slotAllocation,result,call',trace,shape,?_,protectedTree,protectedSize,protectedLen,protectedMask,protectedProv,protectedBytes,protectedMutable⟩
  exact ⟨shape.body.trans (frameBody.trans raw.body),shape.identity.trans (frameIdentity.trans raw.identity),
    shape.callee.trans (frameCallee.trans raw.callee),shape.size,shape.location,shape.slot1.trans sourceOption,
    shape.slot2.trans countOption,shape.slot11,shape.slot12,(congrArg (·.dataRace) shape.extra).trans (frameRace.trans raw.noClocks),
    (congrArg (·.borrowTracker) shape.extra).trans frameBorrow,shape.immediate,
    shape.slot0.trans original0,shape.slot7,shape.slot8,shape.slot10,(shape.keep 13 (by decide)).trans original13,
    shape.slot9,(shape.keep 15 (by decide)).trans original15,(shape.keep 16 (by decide)).trans original16⟩

end DuplicatePrefix.GenericFunctionEntryToShared
