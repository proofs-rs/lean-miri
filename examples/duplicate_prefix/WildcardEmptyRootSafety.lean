import duplicate_prefix.WildcardEmptyRootZeroInvocation
import duplicate_prefix.WildcardEmptyRootNonzeroInvocation
import duplicate_prefix.EmptyRootSafetyEntry
import duplicate_prefix.EmptyRootSafetyToLen
import duplicate_prefix.EmptyRootSafetyExit
import duplicate_prefix.EmptyRootLenCall
import duplicate_prefix.RootInstalledFrame
/-!
# Empty wildcard references below every inverse-map address

For the pinned prepared program and configuration, `invoke` covers every UInt64
count when the input slice has length zero and wildcard provenance. The initial
address is nonnull, the provenance mode is default/permissive, and every existing
inverse-map row has a strictly greater address. The map may contain the concrete
return slot and other allocations. All actual allocation-resolution, retag,
argument-copy and helper-call outcomes are derived from these data.

The statement explicitly requires compiler/runtime metadata, execution options,
tag room, thread state and a canonical writable bool return allocation. Strict
mode, wildcard hits and unknown concrete allocations are outside this theorem.
-/
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.WildcardEmptyRootSafety
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
    (address count : UInt64) (nonzero : address ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel = dynamicFuel+1) (validityEq : options.limits.validation = validityFuel+1)
    (shallow : before.user.payload.validation = .Shallow)
    (addressMode : before.user.addresses.provenanceMode ≠ .strict)
    (below : ∀ entry ∈ before.user.addresses.intToPtrMap, address < entry.address)
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
        #[.Copy (WildcardEmptyRootArguments.first target address),.Copy (WildcardEmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace config limits installed done ∧
      ExecutionMachine.step config limits () done = (done,.ok false) ∧
      CallSafety.NoUBBeforeReturn contextSafety 1 installed := by
  by_cases countZero : count=0
  · subst count
    exact WildcardEmptyRootZeroInvocation.invoke options limits remaining span place layout before tracker enabled initialFresh fresh
      id entry base rootTag pointer aligned cached root size present race distinct unprotected mutable storage maskLength provenance
      noBackend extras ghost target targetEq address nonzero cmp precise implicitWrites debug dynamicFuel validityFuel dynamicEq validityEq shallow addressMode below metadata
      notConstructed thread active noCache source mode unchecked noGc fixed fits
  · exact WildcardEmptyRootNonzeroInvocation.invoke options limits remaining span place layout before tracker enabled initialFresh fresh
      thirdFresh fourthFresh budget dispatch id entry base rootTag pointer aligned cached root size present race distinct unprotected mutable
      storage maskLength provenance noBackend extras ghost target targetEq address count nonzero countZero cmp precise implicitWrites debug dynamicFuel validityFuel
      dynamicEq validityEq shallow addressMode below metadata notConstructed thread active noCache source mode unchecked noGc fixed fits

#print axioms invoke
end DuplicatePrefix.WildcardEmptyRootSafety
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.WildcardEmptyRootSafety.invoke) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved full empty-slice invocation dependency {dependency}"
