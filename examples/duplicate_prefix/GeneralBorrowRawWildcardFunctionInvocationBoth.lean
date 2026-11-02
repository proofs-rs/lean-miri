import duplicate_prefix.GeneralBorrowRawWildcardFunctionInvocation
import duplicate_prefix.RawRootInvocation
namespace DuplicatePrefix.GeneralBorrowRawWildcardFunctionInvocationBoth
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext PositiveRootArguments GeneralBorrowRawWildcardFunctionScope
open TypedBorrowSteps ReferenceBorrowDriver
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem enters
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (tracker : MachineHooks.BorrowState)
    (base len n : UInt64) (nonzero : base ≠ 0)
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
    (noCache : thread.topUserRelevantFrame = none) :
    ∃ output : GeneralBorrowForestFnEntry.Output,
      GeneralBorrowRawWildcardFnEntryRuntime.operation entry.allocation.extra tracker.global {} id 0 len = .ok output ∧
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes (base))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base))) len ActualReferenceMetadata.reference).imm
    let argsFrame := RootArgumentsTwo.result (PositiveRootArguments.firstDone (RawRootInvocation.root before place race) adjusted ({} : FrameState) id tracker.global.nextPointerTag) n
    let argsMachine := resultMachine (RawRootInvocation.machine #[] before) tracker fresh id entry output.child.tree
    let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,tracker.retagMode⟩
    let owned := ({} : FrameState).addProtector id tracker.global.nextPointerTag
    let finalGlobal := (GeneralBorrowFnEntryRegistration.registered next.global owned slotId slotFresh).1
    let changed := {argsFrame.frame with location := FrameLocation.unwinding ⟨601⟩}
    let borrowed := ReturnProtection.borrowedState #[] changed owned argsMachine next slotFresh slotId slotEntry
      (PhysicalMachineWrite.slotTree slotRoot next.global.nextPointerTag 1 false)
    ∃ updated,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩,.Copy (second n)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
      .ok () (Storage.withCurrent #[]
        (CallEntryFacts.doneRootFrame {registeredFrame changed owned slotId next.global.nextPointerTag with location := .unwinding ⟨559⟩})
        (CanonicalCopy.replaceAllocation borrowed slotId slotEntry.kind updated).machine) ∧
      (updated.extra = PhysicalMachineWrite.slotTree slotRoot next.global.nextPointerTag 1 true ∧
      updated.byteSize = Size.ofBytes 1 ∧ updated.len = 1 ∧
      updated.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot slotEntry.allocation ∧
      updated.mutability = .Mut) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree finalGlobal ∧
      ∃ child,output.child.tree.indexOfTag tracker.global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive output.child.tree finalGlobal.protectedTags
          (some child) (some child) (some tracker.global.nextPointerTag) 0 len) := by
  obtain ⟨output,run,updated,entered,properties,rawRuntime,child,lookup,⟨both⟩⟩ :=
    GeneralBorrowRawWildcardFunctionInvocation.enters options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id tracker base len n nonzero entry positive signedFits bounds before ghost shallow cachedAddress present enabled fresh
      position positionValid ordered addressRow addressMode exposedAlloc runtime capability distinct short nodeRoom race metadata notConstructed
      retagCtx place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize slotPresent separate
      slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache
  let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,tracker.retagMode⟩
  let owned := ({} : FrameState).addProtector id tracker.global.nextPointerTag
  let registration := GeneralBorrowFnEntryRegistration.registered tracker.global {} id fresh
  let read := entry.allocation.extra.performBorrowAccessRange .wildcard (Size.ofBytes 0) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  let literal : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,tracker.global.nextPointerTag,read,
    read.tree.newChild (Size.ofBytes 0) .wildcard tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩
  have actualRun : GeneralBorrowRawWildcardFnEntryRuntime.operation entry.allocation.extra tracker.global {} id 0 len = .ok literal := by
    simp only [GeneralBorrowRawWildcardFnEntryRuntime.operation,TypedRetagEmpty.allocate_tag tracker.global fresh,
      Except.bind,Except.pure,bind,pure]
    rfl
  have equal : output = literal := Except.ok.inj (run.symm.trans actualRun)
  have globals : output.global = next.global := by rw [equal];rfl
  rw [globals] at rawRuntime both
  obtain ⟨allocated,held,frameEq,finalRuntime,finalPositive,freshTag⟩ :=
    GeneralBorrowWildcardFnEntryRegistration.prepare output.child.tree next.global owned slotId slotFresh rawRuntime
      (some child) (some child) (some tracker.global.nextPointerTag) 0 len both
  exact ⟨output,run,updated,entered,properties,finalRuntime,child,lookup,finalPositive⟩
end
end DuplicatePrefix.GeneralBorrowRawWildcardFunctionInvocationBoth
