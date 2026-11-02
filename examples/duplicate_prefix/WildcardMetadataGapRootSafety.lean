import duplicate_prefix.WildcardGapRootGeometrySafety
import duplicate_prefix.WildcardMetadataGap

namespace DuplicatePrefix.WildcardMetadataGapRootSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver PhysicalMachineWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Every count's actual invocation from nonnull wildcard empty slices in gaps
certified by raw live, dead, MEMORY or STATIC size metadata. A STATIC descriptor
requires no initializer row here because actual gap lookup never materializes
it. This is a conditional Lean-state result, not a history-reachability claim.
Physical return-slot, runtime and resource contracts are explicit. -/
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
    (address count : UInt64) (nonzero : address ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel = dynamicFuel+1) (validityEq : options.limits.validation = validityFuel+1)
    (shallow : before.user.payload.validation = .Shallow)
    (addressMode : before.user.addresses.provenanceMode ≠ .strict)
    (metadataGeometry : WildcardMetadataGap.Geometry before.user.addresses.intToPtrMap address before.memory)
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
        #[.Copy (WildcardGapRootArguments.first target address),.Copy (WildcardGapRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace config limits installed done ∧
      ExecutionMachine.step config limits () done = (done,.ok false) ∧
      CallSafety.NoUBBeforeReturn contextSafety 1 installed := by
  have data : WildcardGapResolver.Miss before.user.addresses before.memory address :=
    Or.inl (Or.inl (WildcardMetadataGap.geometry before.user.addresses.intToPtrMap address before.memory metadataGeometry))
  exact WildcardGapRootGeometrySafety.invoke
    options limits remaining span place layout before tracker enabled initialFresh fresh thirdFresh fourthFresh budget dispatch id entry base rootTag pointer aligned cached root size present race distinct unprotected mutable storage maskLength provenance noBackend extras ghost target targetEq address count nonzero cmp precise implicitWrites debug dynamicFuel validityFuel dynamicEq validityEq shallow addressMode data metadata notConstructed thread active noCache source mode unchecked noGc fixed fits

end DuplicatePrefix.WildcardMetadataGapRootSafety
