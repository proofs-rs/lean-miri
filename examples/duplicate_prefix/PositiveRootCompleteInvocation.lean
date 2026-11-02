import duplicate_prefix.PositiveRootSuccessInvocation
import duplicate_prefix.PositiveRootCopyEntry
import duplicate_prefix.PositiveRootCopyData
import duplicate_prefix.PositiveRootCopyReturn
import duplicate_prefix.PositiveRootReturnProtection
import duplicate_prefix.PositiveRootTagGrowth
import duplicate_prefix.CanonicalCopyBound

namespace DuplicatePrefix.PositiveRootCompleteInvocation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter Miri.Concurrency
open PhysicalMachineWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Genuine accepted positive-length invocation, including physical true return.
All assumptions describe input/configuration/metadata data, not successful
interpreter operations. Canonical caller topology is still explicit. -/
theorem invoke
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base offset len capacity count : UInt64) (nonzero : base+offset ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounded : len ≤ 9223372036854775807)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (cachedAddress : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (distinct : parentTag ≠ tracker.global.nextPointerTag) (rootUnprotected : tracker.global.protectedTags.contains parentTag = false)
    (tree : entry.allocation.extra = BorrowTree.new parentTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity) (race : before.dataRace = none)
    (metadata : before.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : before.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
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
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (bufferParentDistinct2 : parentTag ≠ TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh)
    (source : PreparedContracts.SourceComparator) (mode : tracker.retagMode = .Default)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user).gcInterval = 0)
    (fixed : before.threads.fixedScheduling = true) (fits : slotBase.toNat+1<2^64)
    (countNonzero : count ≠ 0) (within : count ≤ len/2)
    (tags : Fin 6 → BorTag) (tagsDistinct : Function.Injective tags)
    (parentEq : parentTag = tags 0) (childEq : tracker.global.nextPointerTag = tags 1)
    (thirdFresh : (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag.value < 18446744073709551615)
    (fourthFresh : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag.value < 18446744073709551615)
    (thirdTag : (PositiveRootInvocationState.held tracker fresh slotFresh).global.nextPointerTag = tags 2)
    (fourthTag : (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag = tags 3)
    (newUnprotected : tracker.global.protectedTags.contains (tags 2) = false)
    (slotChildNot2 : (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag ≠ tags 2)
    (slotChildNot3 : (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag ≠ tags 3)
    (slotRootNot3 : slotRoot ≠ tags 3)
    (free4 : tracker.global.protectedTags.contains (tags 4)=false)
    (slotChildNot4 : (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag ≠ tags 4)
    (fifthTag : TypedRetagEmpty.successorTag (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh).global.nextPointerTag fourthFresh=tags 4)
    (fifthFresh : (PositiveLenPost.trackerAfter (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh) fourthFresh id).global.nextPointerTag.value<18446744073709551615)
    (sixthTag : TypedRetagEmpty.successorTag (PositiveLenPost.trackerAfter (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh) fourthFresh id).global.nextPointerTag fifthFresh=tags 5)
    (sixthFresh : (ReferenceBorrowDriver.allocatedTracker (PositiveLenPost.trackerAfter (ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh) fourthFresh id) fifthFresh).global.nextPointerTag.value<18446744073709551615)
    (budget : Nat) (dispatchFuel : limits.callDispatch = budget+1)
    (bufferStorage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (bufferMaskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (bufferMaskLen : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (bufferInitialized : InitMaskCopy.InitializedOn entry.allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+len)))
    (bufferProvenance : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len)
    (bufferStorageFits : entry.allocation.len+64 < 18446744073709551616)
    (bufferMutable : entry.allocation.mutability = .Mut)
    (bufferExtras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (statementFuel : limits.validation = validityFuel+1) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ installed done updated,
      Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance
        RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (ActualReferenceContext.config options remaining span).access.runtime.base
          (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩,
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace config limits installed done ∧
      done.stack.frames = #[] ∧
      ExecutionMachine.step config limits () done = (done,.ok false) ∧
      CallSafety.NoUBBeforeReturn ⟨config,limits,fun _ _ => True⟩ 1 installed ∧
      done.machine.memory.live.find? (fun row => row.1 == slotId) = some (slotId,⟨slotEntry.kind,updated⟩) ∧
      target_bytes config.access.runtime.base (Size.ofBytes 1) 1 = .ok (AllocationCopy.snapshot updated) ∧
      updated.initializationMask = InitMask.new (Size.ofBytes 1) true ∧
      updated.mutability = .Mut := by
  dsimp only
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let slotChild := (PositiveRootInvocationState.next tracker fresh).global.nextPointerTag
  let refTracker := ReferenceBorrowDriver.allocatedTracker (PositiveRootInvocationState.held tracker fresh slotFresh) thirdFresh
  let finalTracker := AsMutRootOutput.held
    (ReferenceBorrowDriver.allocatedTracker (PositiveLenPost.trackerAfter refTracker fourthFresh id) fifthFresh) sixthFresh id

  obtain ⟨initial,initialMachine,caller,machine,call,prefixTrace,shape,post,borrow,
      protectedSlot,slotPresentNow,protectedTree,protectedSize,protectedLen,protectedMask,protectedProv,protectedBytes,protectedMutable,
      metadata,machineMetadata⟩ := PositiveRootSuccessInvocation.invoke options limits remaining span debugOff cmp dynamicFuel validityFuel fuelEq validationEq id parentTag tracker base offset len capacity count nonzero entry positive signedFits bounded bounds before ghost shallow cachedAddress present enabled fresh distinct rootUnprotected tree allocationSize race metadata notConstructed place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize slotPresent separate slotFresh slotDistinct slotParentDistinct slotFree mutable storage maskLength provenance noBackend extras thread active noCache precise implicitWrites bufferParentDistinct2 source mode unchecked noGc fixed fits countNonzero within tags tagsDistinct parentEq childEq thirdFresh fourthFresh thirdTag fourthTag newUnprotected slotChildNot2 slotChildNot3 slotRootNot3 free4 slotChildNot4 fifthTag fifthFresh sixthTag sixthFresh budget dispatchFuel
  let pointer : Scalar Provenance := Scalar.fromPointer config.access.runtime.base (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset)))
  let destination : Scalar Provenance := Scalar.fromPointer config.access.runtime.base (Pointer.new (.concrete id (tags 5)) (Size.ofBytes (base+offset+count)))
  have initialBackend : initialMachine.user.payload.payload.user.backend = .none := machineMetadata.backend.trans noBackend
  let copyEntry := PositiveRootCopyEntry.input options limits remaining span initial caller initialMachine machine pointer destination count
    shape finalTracker {thread with topUserRelevantFrame := some 0} tags id entry capacity offset len post
    debugOff validityFuel validationEq budget dispatchFuel source cmp metadata.body metadata.identity metadata.callee metadata.trackNone
    metadata.noClocks metadata.relevant rfl initialBackend
  have bufferExtrasNow : initialMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩) := by
    rw [machineMetadata.extras]
    exact bufferExtras
  have initialCached : initialMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    rw [machineMetadata.addresses]
    exact cachedAddress
  let data := PositiveRootCopyData.data options remaining span initialMachine machine finalTracker
    {thread with topUserRelevantFrame := some 0} tags id entry base capacity offset len count post
    (UInt64.pos_iff_ne_zero.mpr countNonzero) within bounds allocationSize bufferStorage bufferMaskValid bufferMaskLen bufferInitialized
    bufferProvenance bufferStorageFits bufferMutable bufferExtrasNow initialCached tagsDistinct
    (CanonicalCopyBound.guarded options () (remaining+1) span len count within)
  have refFree : refTracker.global.protectedTags.contains slotRoot = false :=
    PositiveRootInvocationState.buffer_root_free tracker fresh slotFresh slotRoot slotParentDistinct slotDistinct slotFree
  have finalFree : finalTracker.global.protectedTags.contains slotRoot = false :=
    PositiveRootReturnProtection.two_helpers_free refTracker fourthFresh id fifthFresh sixthFresh slotRoot refFree
  have refHeld : refTracker.global.protectedTags.contains slotChild = true := by
    change ((tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).insert slotChild .StrongProtector).contains slotChild = true
    simp [ProtectedTags.contains]
  have different3 : slotChild ≠ refTracker.global.nextPointerTag := by
    rw [fourthTag]
    exact slotChildNot3
  have different5 : slotChild ≠ (ReferenceBorrowDriver.allocatedTracker (PositiveLenPost.trackerAfter refTracker fourthFresh id) fifthFresh).global.nextPointerTag := by
    change slotChild ≠ TypedRetagEmpty.successorTag (PositiveLenPost.trackerAfter refTracker fourthFresh id).global.nextPointerTag fifthFresh
    exact PositiveRootTagGrowth.slot_child_not_last tracker fresh slotFresh thirdFresh fourthFresh id fifthFresh
  have finalHeld : finalTracker.global.protectedTags.contains slotChild = true :=
    (PositiveRootReturnProtection.two_helpers_other refTracker fourthFresh id fifthFresh sixthFresh slotChild different3 different5).trans refHeld
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have innerFields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨outer,outerAccess,outerArithmetic,_⟩ := fields.canonicalCopy
  obtain ⟨inner,innerAccess,innerArithmetic,_⟩ := innerFields.canonicalCopy
  have outerWidth : outer.pointers.arithmetic = ⟨Size.ofBytes 8⟩ := outerArithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () (remaining+1) span)
  have innerWidth : inner.pointers.arithmetic = ⟨Size.ofBytes 8⟩ := innerArithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () remaining span)
  have outerRuntime : outer.access.runtime = PreparedReflection.actual.runtime.target :=
    (congrArg (fun access => access.runtime) outerAccess).symm.trans (CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span)
  have innerRuntime : inner.access.runtime = PreparedReflection.actual.runtime.target :=
    (congrArg (fun access => access.runtime) innerAccess).symm.trans (CanonicalConfigFacts.actual_access_runtime options () remaining span)
  have frameTracked : initial.extra.borrowTracker = some (RootSuccessReleaseProfile.frame id tags slotId slotChild) := by
    rw [←shape.extra]
    simpa only [RootSuccessReleaseProfile.frame,childEq] using borrow
  have slotCachedNow : machine.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩ := by
    rw [post.addresses,machineMetadata.addresses]
    exact slotCached
  have slotExtrasNow : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩) := by
    rw [post.extras,machineMetadata.extras]
    exact extras
  let input : PositiveRootCopyReturn.Input := {
    options := options,limits := limits,remaining := remaining,span := span,before := initial,caller := caller,machine := machine
    pointer := pointer,destinationValue := destination,count := count,entry := copyEntry,data := data
    statementFuel := statementFuel,defaultMode := mode,context := outer,validationContext := inner
    accessEq := innerAccess,validationWidth := innerWidth,validationRuntimeSize := by rw [innerRuntime];rfl
    sameRuntime := by rw [innerRuntime,outerRuntime]
    width := outerWidth,runtimeWidth := by rw [outerRuntime];rfl
    runtimeSize := by rw [outerRuntime];rfl
    outerAccessEq := outerAccess,shape := shape,zero := metadata.zero,body := metadata.body,identity := metadata.identity,callee := metadata.callee
    noLocalClocks := metadata.noClocks,continuation := metadata.continuation,varargs := metadata.varargs
    slotId := slotId,separate := separate,slot := {slotEntry with allocation := protectedSlot},slotPresent := slotPresentNow
    slotRoot := slotRoot,slotChild := slotChild,slotTree := protectedTree,slotRootFree := finalFree,slotChildHeld := finalHeld
    slotDistinct := slotDistinct,frameTracked := frameTracked,slotSize := protectedSize,slotStorage := protectedLen
    slotMask := protectedMask,slotProvenance := protectedProv,slotMutable := protectedMutable
    place := place,layout := layout,slotBase := slotBase,slotPointer := slotPointer,aligned := aligned,fits := fits
    cached := slotCachedNow,extras := slotExtrasNow,destination := by rw [metadata.returnPlace];rfl }
  obtain ⟨done,written,tail,terminal,tailSafe,empty,stored,writtenTree,writtenSize,writtenLen,writtenMask,writtenProv,encoded,writtenMutable⟩ :=
    PositiveRootCopyReturn.complete input
  have tailTrace : SuccessfulTrace.Trace config limits (Storage.withCurrent #[] caller machine) done := tail
  have fullTrace := SuccessfulTrace.append prefixTrace tailTrace
  have safe : CallSafety.NoUBBeforeReturn ⟨config,limits,fun _ _ => True⟩ 1 (Storage.withCurrent #[] initial initialMachine) :=
    SuccessfulTrace.no_ub ⟨config,limits,fun _ _ => True⟩ 1 _ done ⟨by decide,rfl⟩ fullTrace
      (by unfold CallSafety.pastCallBoundary CallSafety.frameDepth;rw [empty];decide)
  have encoding : target_bytes config.access.runtime.base (Size.ofBytes 1) 1 = .ok (AllocationCopy.snapshot written) := by
    change target_bytes outer.access.runtime.base protectedSlot.byteSize 1 = .ok (AllocationCopy.snapshot written) at encoded
    rw [←outerAccess,protectedSize] at encoded
    exact encoded
  have initialized : written.initializationMask = InitMask.new (Size.ofBytes 1) true := by
    change written.initializationMask = InitMask.new protectedSlot.byteSize true at writtenMask
    rw [protectedSize] at writtenMask
    exact writtenMask
  exact ⟨Storage.withCurrent #[] initial initialMachine,done,written,call,fullTrace,empty,terminal,safe,stored,encoding,initialized,writtenMutable.trans protectedMutable⟩

end DuplicatePrefix.PositiveRootCompleteInvocation
#print axioms DuplicatePrefix.PositiveRootCompleteInvocation.invoke
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.PositiveRootCompleteInvocation.invoke) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved whole successful invocation dependency {dependency}"
