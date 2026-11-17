import duplicate_prefix.WildcardGlobalEmptyRootCallEquivalence
import duplicate_prefix.WildcardStaticEmptyRootCallEquivalence
import duplicate_prefix.DuplicatePrefixCallSpecification
import duplicate_prefix.WildcardGlobalEmptyRootArgumentScope
import duplicate_prefix.GlobalEmptyRootPrepared
import duplicate_prefix.WildcardPoolHitRootArgumentScope
import duplicate_prefix.RawRootInvocation

namespace DuplicatePrefix.S03MaterializableWildcardCallEquivalence
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext ConcreteEmptyRootArguments ConcreteEmptyRootArgumentScope
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The original wildcard call executes the selected lazy image prefix.
This exact equality retains all validation and source-order materialization. -/
theorem call_eq
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
    (distinct : parentTag ≠ tracker.global.nextPointerTag)
    (source : Allocation CtfeProvenance Unit) (supported : GlobalSupportedImage.Supported source PreparedReflection.actual.compiler.runtime.target
      before.memory tracker.global.rootPointerTags before.user.addresses.baseAddr)
    (rootCached : tracker.global.rootTag? id = some parentTag) (race : before.dataRace = none)
    (noExtras : (before.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (absent : before.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : before.memory.hasFunctionPointer id = false) (noVaList : before.memory.hasVaListId id = false)
    (descriptor : DuplicatePrefixEmptyReferenceInput.ImageDescriptor
      (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory id source)
    (addressMode : before.user.addresses.provenanceMode ≠ .strict)
    (geometry : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap (base+offset) base id source.byteSize)
    (exposed : before.user.addresses.exposed.contains id = true)
    (allocLive : before.memory.isAllocLive id = true)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (place : MPlaceTy Provenance) (thread : Miri.Concurrency.ThreadRecord)
    (active : before.threads.activeThread? = some thread) (noCache : thread.topUserRelevantFrame = none) :
    ∃ converted : Allocation Provenance Unit, GlobalAllocationAttributes.Attributes source converted ∧
      let h := ExecutionMachine.callHooks (config options (remaining+1) span) limits
      let first : OpTy Provenance := ⟨.immediate (RetagReferencePlace.sliceValue
        (config options remaining span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes (base+offset))) 0 ActualReferenceMetadata.reference).imm,
        ActualReferenceMetadata.reference⟩
      Call.initStackFrame h () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy first,.Copy (second n)] false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ =
      Call.initStackFrame h () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy first,.Copy (second n)] false (.memory place) (.stop true)
          ⟨⟨#[]⟩,WildcardGlobalEmptyRootCopy.preparedMachine options before id parentTag source converted⟩ := by
  rcases descriptor with memoryDescriptor | ⟨definition,initializer,staticDescriptor⟩
  · exact WildcardGlobalEmptyRootCallEquivalence.call_eq options limits remaining span ctx actualPointers debugOff cmp
      dynamicFuel validityFuel fuelEq validationEq id parentTag tracker base offset n nonzero before ghost shallow cachedAddress
      enabled fresh distinct source supported rootCached race noExtras absent noFunction noVaList memoryDescriptor addressMode
      geometry exposed allocLive metadata notConstructed place thread active noCache
  · exact WildcardStaticEmptyRootCallEquivalence.call_eq options limits remaining span ctx actualPointers debugOff cmp
      dynamicFuel validityFuel fuelEq validationEq id parentTag tracker base offset n nonzero before ghost shallow cachedAddress
      enabled fresh distinct source definition initializer supported rootCached race noExtras absent noFunction noVaList staticDescriptor
      addressMode geometry exposed allocLive metadata notConstructed place thread active noCache
end
end DuplicatePrefix.S03MaterializableWildcardCallEquivalence
