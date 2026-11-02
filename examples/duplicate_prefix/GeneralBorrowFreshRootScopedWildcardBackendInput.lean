import duplicate_prefix.GeneralBorrowRawWildcardFunctionStorage
import duplicate_prefix.GeneralBorrowFreshRootScopedWildcardToShared
import duplicate_prefix.GeneralBorrowRawWildcardFnEntryScopedResources
import duplicate_prefix.GeneralBorrowFreshRootScopedShared
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedWildcardBackendInput
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
open GeneralBorrowRawWildcardFunctionToShared (Ready)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- The actual original wildcard caller reaches PC2:11 and forms the next
shared-Ref input internally from the installed source tree. Only initial
numeric headroom is added; there is no global tag-order or future Input premise. -/
theorem enters_shared_boundary
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (tracker : MachineHooks.BorrowState)
    (base len count : UInt64) (nonzero : base ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (position : Nat) (positionValid : position < before.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered before.user.addresses.intToPtrMap)
    (addressRow : before.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (addressMode : before.user.addresses.provenanceMode ≠ .strict)
    (exposedAlloc : before.user.addresses.exposed.contains id = true)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (capability : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags none none none 0 len)
    (distinct : entry.allocation.extra.roots.toList.Nodup)
    (short : entry.allocation.extra.nodes.size < 65536)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295)
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
    (fixed : before.threads.fixedScheduling = true)
    (nodeHeadroom : entry.allocation.extra.nodes.size+1 < 65536)
    (tagHeadroom : tracker.global.nextPointerTag.value.toNat+2 < 18446744073709551615) :
    ∃ output : GeneralBorrowForestFnEntry.Output,
      GeneralBorrowRawWildcardFnEntryRuntime.operation entry.allocation.extra tracker.global {} id 0 len = .ok output ∧
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let adjusted := (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base))) len ActualReferenceMetadata.reference).imm
    let frame := PositiveRootInstalledFrame.installed (RawRootInvocation.root before place race) adjusted count {} id tracker.global.nextPointerTag
      slotId (GeneralBorrowRawWildcardFunctionState.next tracker fresh).global.nextPointerTag
    ∃ (slotAllocation : Allocation Provenance BorrowTree) (result : CompilerFrameContext.ActualFrame),
      let initialMachine := GeneralBorrowRawWildcardFunctionState.enteredMachine (RawRootInvocation.machine #[] before) tracker fresh id entry output.child.tree
        slotFresh slotId slotEntry slotRoot slotAllocation
      Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes (base))) len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
        .ok () (Storage.withCurrent #[] frame initialMachine) ∧
      SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame initialMachine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span initialMachine)) ∧
      GenericFunctionEntryPrefix.Shape frame result count ∧
      Ready result adjusted count ((({} : FrameState).addProtector id tracker.global.nextPointerTag).addProtector
        slotId (GeneralBorrowRawWildcardFunctionState.next tracker fresh).global.nextPointerTag) ∧
      (slotAllocation.extra = PhysicalMachineWrite.slotTree slotRoot (GeneralBorrowRawWildcardFunctionState.next tracker fresh).global.nextPointerTag 1 true ∧
      slotAllocation.byteSize = Size.ofBytes 1 ∧ slotAllocation.len = 1 ∧
      slotAllocation.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      slotAllocation.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot slotAllocation = AllocationCopy.snapshot slotEntry.allocation ∧
      slotAllocation.mutability = .Mut) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree
        (TypedRetagGeneric.protectedGlobal (GeneralBorrowRawWildcardFunctionState.next tracker fresh).global slotFresh) ∧
      (RootZeroCompleteState.tick options remaining span initialMachine).memory.live.find? (fun row => row.1 == id) =
        some (id,{entry with allocation := entry.allocation.setExtra output.child.tree}) ∧
      (RootZeroCompleteState.tick options remaining span initialMachine).borrowTracker =
        some (GeneralBorrowRawWildcardFunctionState.held tracker fresh slotFresh) ∧
      ∃ child,output.child.tree.indexOfTag tracker.global.nextPointerTag = some child ∧
        Nonempty (GeneralBorrowFreshRootScopedRow.Positive output.child.tree
          (TypedRetagGeneric.protectedGlobal (GeneralBorrowRawWildcardFunctionState.next tracker fresh).global slotFresh).protectedTags
          child child tracker.global.nextPointerTag 0 len) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write 0 len ∧
        ∃ input : GeneralBorrowFreshRootScopedShared.Input output.child.tree
            (TypedRetagGeneric.protectedGlobal (GeneralBorrowRawWildcardFunctionState.next tracker fresh).global slotFresh),
          input.parentTag = tracker.global.nextPointerTag ∧ input.parent = child ∧ input.selected = child ∧
          input.maximum = tracker.global.nextPointerTag ∧ input.offset = 0 ∧ input.len = len := by
  obtain ⟨output,run,slotAllocation,result,call,trace,shape,ready,slotProperties,currentRuntime,child,lookup,⟨owner⟩,activity⟩ :=
    GeneralBorrowFreshRootScopedWildcardToShared.enters_shared_boundary options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id tracker base len count nonzero entry positive signedFits bounds before ghost shallow cachedAddress present enabled fresh
      position positionValid ordered addressRow addressMode exposedAlloc runtime capability distinct short nodeRoom race metadata notConstructed
      retagCtx place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize slotPresent separate
      slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache
      source mode countPositive unchecked noGc fixed
  obtain ⟨resourceOutput,resourceRun,tagEq,globalEq,frameEq,readDone,childDone,rawRuntime,capacity,growth,rootDistinct,resourceChild,resourceLookup,roots,resourceOwner,resourceActivity,geometry⟩ :=
    GeneralBorrowRawWildcardFnEntryScopedResources.invoke entry.allocation.extra tracker.global {} id runtime 0 len capability distinct short nodeRoom fresh
  have same : resourceOutput = output := Except.ok.inj (resourceRun.symm.trans run)
  subst resourceOutput
  let fullGlobal := TypedRetagGeneric.protectedGlobal (GeneralBorrowRawWildcardFunctionState.next tracker fresh).global slotFresh
  obtain ⟨readOwner⟩ := GeneralBorrowFreshRootScopedReadRow.of_positive output.child.tree fullGlobal.protectedTags child child
    tracker.global.nextPointerTag 0 len owner
  have currentShort : output.child.tree.nodes.size < 65536 := by omega
  have currentRoom : fullGlobal.nextPointerTag.value < 18446744073709551615 := by
    change (TypedRetagEmpty.successorTag (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh) slotFresh).value < 18446744073709551615
    apply UInt64.lt_iff_toNat_lt.mpr
    have first := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
    have second := GenericFunctionEntryNumerics.successor_value (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh) slotFresh
    change (TypedRetagEmpty.successorTag (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh) slotFresh).value.toNat < 18446744073709551615
    omega
  let input : GeneralBorrowFreshRootScopedShared.Input output.child.tree fullGlobal := {
    parentTag := tracker.global.nextPointerTag,parent := child,selected := child,maximum := tracker.global.nextPointerTag,
    offset := 0,len := len,tagged := lookup,positive := readOwner,distinct := rootDistinct,
    short := currentShort,nodeRoom := by omega,tagRoom := currentRoom }
  have stored := GeneralBorrowRawWildcardFunctionStorage.current options remaining span (RawRootInvocation.machine #[] before)
    tracker fresh id entry output.child.tree slotFresh slotId slotEntry slotRoot slotAllocation (Ne.symm separate)
  exact ⟨output,run,slotAllocation,result,call,trace,shape,ready,slotProperties,currentRuntime,stored.2.1,stored.2.2.1,child,lookup,⟨owner⟩,activity,
    input,rfl,rfl,rfl,rfl,rfl,rfl⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedWildcardBackendInput
