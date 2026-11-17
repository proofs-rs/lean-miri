import duplicate_prefix.S03MaterializableCallEquivalence
import duplicate_prefix.S03MaterializableWildcardCallEquivalence
import duplicate_prefix.S03MaterializableInput

namespace DuplicatePrefix.S03MaterializableCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext ConcreteEmptyRootArguments
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The original concrete call's lazy-image prefix is derived from the initial
Materializable alternative. The prepared call is the exact reduction target;
no prepared-state Contract, Resources or successful call is assumed. -/
theorem concrete
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset n : UInt64) (nonzero : base+offset ≠ 0)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (candidate : DuplicatePrefixEmptyReferenceInput.Materializable (imageContext options before tracker)
      before.memory before.user.addresses id (some parentTag))
    (below : ∀ row ∈ tracker.global.rootPointerTags.toList, row.2.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (race : before.dataRace = none)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (place : MPlaceTy Provenance) (thread : Miri.Concurrency.ThreadRecord)
    (active : before.threads.activeThread? = some thread) (noCache : thread.topUserRelevantFrame = none) :
    ∃ packet : S03MaterializableInput.Packet options before tracker id (some parentTag),
      ∃ converted : Allocation Provenance Unit, GlobalAllocationAttributes.Attributes packet.source converted ∧
      let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
      let first : OpTy Provenance := ⟨.immediate (RetagReferencePlace.sliceValue
        (config options remaining span).access.runtime.base
        (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm,
        ActualReferenceMetadata.reference⟩
      Call.initStackFrame h () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy first,.Copy (second n)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
      Call.initStackFrame h () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy first,.Copy (second n)] false (.memory place) (.stop true)
          ⟨⟨#[]⟩,GlobalEmptyRootCopy.preparedMachine options before id packet.root packet.source converted⟩ := by
  obtain ⟨packet⟩ := S03MaterializableInput.of_input options before tracker id (some parentTag) candidate below
  have same : parentTag = packet.root := by
    rcases packet.agreement with impossible | equal
    · cases impossible
    · exact Option.some.inj equal
  obtain ⟨converted,attributes,actual⟩ := S03MaterializableCallEquivalence.call_eq options limits remaining span ctx actualPointers
    debugOff cmp dynamicFuel validityFuel fuelEq validationEq id packet.root tracker base offset n nonzero before ghost shallow
    cachedAddress enabled fresh packet.distinct packet.source packet.supported packet.rootCached race packet.noExtras packet.absent
    packet.noFunction packet.noVaList packet.descriptor metadata notConstructed place thread active noCache
  exact ⟨packet,converted,attributes,by simpa only [same] using actual⟩

/-- The selected original wildcard hit derives the matching source-image size
and executes the actual lazy-image prefix before the same live-call reduction. -/
theorem wildcard
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (actualPointers : ctx.pointers = GlobalDataOnlyActualConfig.pointers PreparedReflection.actual.compiler
      PreparedReflection.actual.image (Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions) ())
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (tracker : MachineHooks.BorrowState)
    (base offset n : UInt64) (nonzero : base+offset ≠ 0)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (candidate : DuplicatePrefixEmptyReferenceInput.Materializable (imageContext options before tracker)
      before.memory before.user.addresses id none)
    (below : ∀ row ∈ tracker.global.rootPointerTags.toList, row.2.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (race : before.dataRace = none)
    (info : AllocationInfo) (known : before.memory.getAllocInfo id = .ok info)
    (addressMode : before.user.addresses.provenanceMode ≠ .strict)
    (geometry : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap (base+offset) base id info.size)
    (exposed : before.user.addresses.exposed.contains id = true)
    (allocLive : before.memory.isAllocLive id = true)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (place : MPlaceTy Provenance) (thread : Miri.Concurrency.ThreadRecord)
    (active : before.threads.activeThread? = some thread) (noCache : thread.topUserRelevantFrame = none) :
    ∃ packet : S03MaterializableInput.Packet options before tracker id none,
      ∃ converted : Allocation Provenance Unit, GlobalAllocationAttributes.Attributes packet.source converted ∧
      let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
      let first : OpTy Provenance := ⟨.immediate (RetagReferencePlace.sliceValue
        (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm,
        ActualReferenceMetadata.reference⟩
      Call.initStackFrame h () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy first,.Copy (second n)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
      Call.initStackFrame h () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy first,.Copy (second n)] false (.memory place) (.stop true)
          ⟨⟨#[]⟩,WildcardGlobalEmptyRootCopy.preparedMachine options before id packet.root packet.source converted⟩ := by
  obtain ⟨packet⟩ := S03MaterializableInput.of_input options before tracker id none candidate below
  have infoEq : info = ⟨packet.source.byteSize,packet.source.align,.liveData,packet.source.mutability⟩ :=
    Except.ok.inj (known.symm.trans packet.alloc_info)
  have size : info.size = packet.source.byteSize := congrArg AllocationInfo.size infoEq
  rw [size] at geometry
  obtain ⟨converted,attributes,actual⟩ := S03MaterializableWildcardCallEquivalence.call_eq options limits remaining span ctx actualPointers
    debugOff cmp dynamicFuel validityFuel fuelEq validationEq id packet.root tracker base offset n nonzero before ghost shallow
    cachedAddress enabled fresh packet.distinct packet.source packet.supported packet.rootCached race packet.noExtras packet.absent
    packet.noFunction packet.noVaList packet.descriptor addressMode geometry exposed allocLive metadata notConstructed place thread active noCache
  exact ⟨packet,converted,attributes,actual⟩

end
end DuplicatePrefix.S03MaterializableCall
