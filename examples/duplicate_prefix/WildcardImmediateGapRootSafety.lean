import duplicate_prefix.WildcardGapRootGeometrySafety
import duplicate_prefix.WildcardImmediateGapAddress
import duplicate_prefix.DuplicatePrefixCompletedCallResult

namespace DuplicatePrefix.WildcardImmediateGapRootSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver PhysicalMachineWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Common all-count actual-call result for a nonstrict wildcard empty miss, with only the selected predecessor outside its metadata size.
Every initial premise is retained from WildcardEmptyRootSafety.invoke; no target
success, physical return, final permission or execution history is supplied by
the caller. The adapter derives NoErrors, final empty stack and every-prefix
step success. General empty-reference coverage remains a separate obligation. -/
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
    (gap : WildcardImmediateGapAddress.RawGeometry before.memory before.user.addresses address)
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
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 count place := by
  have miss : WildcardGapResolver.Miss before.user.addresses before.memory address :=
    Or.inl (Or.inr (WildcardImmediateGapAddress.geometry_of_raw before.memory before.user.addresses address gap))
  obtain ⟨installed, done, call, trace, terminal, safety⟩ := WildcardGapRootGeometrySafety.invoke
      options limits remaining span place layout before tracker
      enabled initialFresh fresh thirdFresh fourthFresh budget dispatch id
      entry base rootTag pointer aligned cached root size
      present race distinct unprotected mutable storage maskLength provenance
      noBackend extras ghost target targetEq address count nonzero
      cmp precise implicitWrites debug dynamicFuel validityFuel dynamicEq validityEq
      shallow addressMode miss metadata notConstructed thread active noCache
      source mode unchecked noGc fixed fits
  rw [targetEq] at call
  exact DuplicatePrefixCompletedCallResult.of_trace options limits remaining span before
    (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0 count place installed done call safety.1 trace terminal

end
end DuplicatePrefix.WildcardImmediateGapRootSafety
