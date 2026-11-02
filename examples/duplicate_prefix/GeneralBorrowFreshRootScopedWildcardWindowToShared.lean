import duplicate_prefix.GeneralBorrowRawWildcardWindowReady
import duplicate_prefix.GeneralBorrowRawWildcardWindowFunctionToShared
import duplicate_prefix.GeneralBorrowRawWildcardFnEntryScoped
import duplicate_prefix.GeneralBorrowFreshRootScopedRegistration
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedWildcardWindowToShared
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
open GeneralBorrowRawWildcardFunctionToShared (Ready)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Original wildcard invocation reaches PC2:11 with the refined bounded-support
capability needed by flexible concrete operations, under the final actual two
protector global. Its real caller and trace are reused, not future premises. -/
theorem enters_shared_boundary
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (tracker : MachineHooks.BorrowState)
    (address base len count : UInt64) (nonzero : address ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : (address-base).toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (position : Nat)
    (addressGeometry : WildcardInteriorHitAddress.Cut before.user.addresses.intToPtrMap address (position+1))
    (insideAddress : address-base < entry.allocation.byteSize.bytes)
    (addressRow : before.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (addressMode : before.user.addresses.provenanceMode ≠ .strict)
    (exposedAlloc : before.user.addresses.exposed.contains id = true)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (capability : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags none none none (address-base) len)
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
    (fixed : before.threads.fixedScheduling = true) :
    ∃ output : GeneralBorrowForestFnEntry.Output,
      GeneralBorrowRawWildcardFnEntryRuntime.operation entry.allocation.extra tracker.global {} id (address-base) len = .ok output ∧
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let adjusted := (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
    let frame := PositiveRootInstalledFrame.installed (RawRootInvocation.root before place race) adjusted count {} id tracker.global.nextPointerTag
      slotId (GeneralBorrowRawWildcardWindowFunctionState.next tracker fresh).global.nextPointerTag
    ∃ (slotAllocation : Allocation Provenance BorrowTree) (result : CompilerFrameContext.ActualFrame),
      let initialMachine := GeneralBorrowRawWildcardWindowFunctionState.enteredMachine (RawRootInvocation.machine #[] before) tracker fresh id entry output.child.tree
        slotFresh slotId slotEntry slotRoot slotAllocation
      Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
          (Pointer.new .wildcard (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
        .ok () (Storage.withCurrent #[] frame initialMachine) ∧
      SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame initialMachine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span initialMachine)) ∧
      GenericFunctionEntryPrefix.Shape frame result count ∧
      Ready result adjusted count ((({} : FrameState).addProtector id tracker.global.nextPointerTag).addProtector
        slotId (GeneralBorrowRawWildcardWindowFunctionState.next tracker fresh).global.nextPointerTag) ∧
      (slotAllocation.extra = PhysicalMachineWrite.slotTree slotRoot (GeneralBorrowRawWildcardWindowFunctionState.next tracker fresh).global.nextPointerTag 1 true ∧
      slotAllocation.byteSize = Size.ofBytes 1 ∧ slotAllocation.len = 1 ∧
      slotAllocation.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      slotAllocation.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot slotAllocation = AllocationCopy.snapshot slotEntry.allocation ∧
      slotAllocation.mutability = .Mut) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree
        (TypedRetagGeneric.protectedGlobal (GeneralBorrowRawWildcardWindowFunctionState.next tracker fresh).global slotFresh) ∧
      ∃ child,output.child.tree.indexOfTag tracker.global.nextPointerTag = some child ∧
        Nonempty (GeneralBorrowFreshRootScopedRow.Positive output.child.tree
          (TypedRetagGeneric.protectedGlobal (GeneralBorrowRawWildcardWindowFunctionState.next tracker fresh).global slotFresh).protectedTags
          child child tracker.global.nextPointerTag (address-base) len) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write (address-base) ((address-base)+len) := by
  obtain ⟨output,run,slotAllocation,result,call,trace,shape,ready,slotProperties,baseRuntime,child,lookup,basePositive,activity⟩ :=
    GeneralBorrowRawWildcardWindowFunctionToShared.enters_shared_boundary options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id tracker address base len count nonzero entry positive signedFits bounds before ghost shallow cachedAddress present enabled fresh
      position addressGeometry insideAddress addressRow addressMode exposedAlloc runtime capability distinct short nodeRoom race metadata notConstructed
      retagCtx place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize slotPresent separate
      slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache
      source mode countPositive unchecked noGc fixed
  obtain ⟨resourceOutput,resourceRun,tagEq,globalEq,frameEq,readDone,childDone,rawRuntime,capacity,growth,resourceChild,resourceLookup,roots,⟨owner⟩,resourceActivity,geometry⟩ :=
    GeneralBorrowRawWildcardFnEntryScoped.invoke entry.allocation.extra tracker.global {} id runtime (address-base) len capability distinct short nodeRoom fresh
  have same : resourceOutput = output := Except.ok.inj (resourceRun.symm.trans run)
  subst resourceOutput
  rw [tagEq] at resourceLookup owner
  have childSame : resourceChild = child := Option.some.inj (resourceLookup.symm.trans lookup)
  subst resourceChild
  let next : MachineHooks.BorrowState := GeneralBorrowRawWildcardWindowFunctionState.next tracker fresh
  let owned := ({} : FrameState).addProtector id tracker.global.nextPointerTag
  have globals : output.global = next.global := globalEq
  rw [globals] at rawRuntime owner
  obtain ⟨allocated,held,pushed,finalRuntime,finalPositive,freshTag⟩ :=
    GeneralBorrowFreshRootScopedRegistration.prepare output.child.tree next.global owned slotId slotFresh rawRuntime
      child child tracker.global.nextPointerTag (address-base) len owner
  exact ⟨output,run,slotAllocation,result,call,trace,shape,GeneralBorrowRawWildcardWindowReady.to_base ready,slotProperties,finalRuntime,child,lookup,finalPositive,activity⟩
end DuplicatePrefix.GeneralBorrowFreshRootScopedWildcardWindowToShared
