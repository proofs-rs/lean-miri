import duplicate_prefix.RootZeroInvocationState
import duplicate_prefix.WildcardGapRootInstalledFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.WildcardGapRootZeroInvocation
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
    (address : UInt64) (nonzero : address ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel = dynamicFuel+1) (validityEq : options.limits.validation = validityFuel+1)
    (shallow : before.user.payload.validation = .Shallow)
    (addressMode : before.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardGapResolver.Miss before.user.addresses before.memory address)
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
        #[.Copy (WildcardGapRootArguments.first target address),.Copy (WildcardGapRootArguments.second 0)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace config limits installed done ∧
      ExecutionMachine.step config limits () done = (done,.ok false) ∧
      CallSafety.NoUBBeforeReturn contextSafety 1 installed := by
  dsimp only
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  obtain ⟨ctx⟩ := ActualRetagContext.exists_context options (remaining+1) span precise implicitWrites
  obtain ⟨slotAllocation,call,protectedTree,protectedSize,protectedLen,protectedMask,protectedProv,protectedBytes,protectedMutable⟩ :=
    WildcardGapRootInvocationEntry.enters options limits remaining span ctx place layout before tracker enabled initialFresh fresh
      id entry base rootTag pointer aligned cached root size present race distinct unprotected mutable storage maskLength provenance
      noBackend extras ghost target targetEq address 0 nonzero cmp precise implicitWrites debug dynamicFuel validityFuel dynamicEq validityEq shallow addressMode miss metadata
      notConstructed thread active noCache
  let raw := RawRootInvocation.root before place race
  let rawMachine := RawRootInvocation.machine #[] before
  let tag := RootZeroInvocationState.child tracker initialFresh
  let heldTracker := RootZeroInvocationState.held tracker initialFresh fresh
  let frame := WildcardGapRootInstalledFrame.installed raw target address 0 {} id tag
  let initialMachine := RootZeroInvocationState.enteredMachine rawMachine tracker initialFresh fresh id entry rootTag slotAllocation
  have call' : Call.initStackFrame (ExecutionMachine.callHooks config limits) () RootBody.reflected.functionInstance
      RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (WildcardGapRootArguments.first target address),.Copy (WildcardGapRootArguments.second 0)] false (.memory place) (.stop true)
      ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame initialMachine) := by
    rw [RootZeroInvocationState.entered_eq] at call
    exact call
  obtain ⟨frameBody,frameIdentity,frameCallee,frameContinuation,frameReturn,frameVa,frameRace,frameBorrow,frameLocation⟩ :=
    WildcardGapRootInstalledFrame.metadata raw target address 0 {} id tag
  have frameSize : frame.locals.size=25 := WildcardGapRootInstalledFrame.size raw target address 0 {} id tag
  have valid0 : (0:MIR.LocalId)<frame.locals.size := by rw [frameSize];decide
  have slot0 := WildcardGapRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) target address 0 {} id tag ⟨0,by decide⟩
  have slot2 := WildcardGapRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) target address 0 {} id tag ⟨2,by decide⟩
  have slot3 := WildcardGapRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) target address 0 {} id tag ⟨3,by decide⟩
  have slot4 := WildcardGapRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) target address 0 {} id tag ⟨4,by decide⟩
  have slot5 := WildcardGapRootInstalledFrame.slot raw (RawRootInvocation.locals before place race) target address 0 {} id tag ⟨5,by decide⟩
  simp only [Fin.val_mk,eq_self_iff_true,Nat.reduceEqDiff,or_true,or_false,true_or,false_or,ite_true,ite_false] at slot0 slot2 slot3 slot4 slot5
  have allImmediate := WildcardGapRootInstalledFrame.immediate raw (RawRootInvocation.locals before place race) target address 0 {} id tag
  let bM := RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span initialMachine))
  let newEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation:=slotAllocation}
  let bf : FrameState := ({} : FrameState).addProtector id tag
  let releasedMemory := StackPopRelease.commitTree bM.memory id newEntry slotAllocation.extra
  let postTracker := {heldTracker with global:=heldTracker.global.endCall bf}
  let popped := GenericPopFrame.afterRelevanceAt #[] frame (ActualPopPlan.released bM releasedMemory heldTracker bf) 0
  let state : MachineHooks.State MiriMemoryKind Machine.RootUser := ⟨⟨#[]⟩,popped⟩
  have heldFree := RootZeroInvocationState.held_root_free tracker initialFresh fresh rootTag distinct unprotected
  have heldChild := RootZeroInvocationState.held_child tracker initialFresh fresh
  have initialPresent : initialMachine.memory.live.find? (fun row => row.1 == id)=some (id,newEntry) :=
    RootZeroInvocationState.entered_lookup rawMachine tracker initialFresh fresh id entry rootTag slotAllocation
  have profile : RootPhysicalReturnPlan.Profile heldTracker.global.protectedTags bf.protectedTags.toList bM.memory releasedMemory := by
    apply RootPhysicalReturnPlan.Profile.slot id rootTag tag 1 true newEntry [] bM.memory releasedMemory
      initialPresent protectedTree heldFree heldChild distinct (by decide)
    exact .nil _
  have rawActive : rawMachine.threads.activeThread?=some {thread with topUserRelevantFrame:=some 0} :=
    PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 thread 0 active
  have activeEntered : bM.threads.activeThread?=some {thread with topUserRelevantFrame:=some 0} := rawActive
  have rawFacts := RawRootInvocation.preservation #[] before
  have addrState : state.machine.user.addresses=before.user.addresses := by
    change bM.user.addresses=before.user.addresses
    dsimp only [bM]
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.1]
    exact rawFacts.2.2.2.1
  have backendState : state.machine.user.payload.payload.user.backend=.none := by
    change bM.user.payload.payload.user.backend=.none
    dsimp only [bM]
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.1]
    exact rawFacts.2.2.2.2.2.2.2.1.trans noBackend
  have extrasState : state.machine.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras := by
    change bM.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras
    dsimp only [bM]
    rw [(RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2,
      (RootZeroInvocationState.tick_fields options remaining span _).2.2.2.2.2.2]
    exact rawFacts.2.2.2.2.2.2.2.2
  have initialGhost : initialMachine.user.payload.ghost=false := rawFacts.2.2.2.2.1.trans ghost
  have initialShallow : initialMachine.user.payload.validation=.Shallow := rawFacts.2.2.2.2.2.1.trans shallow
  have ghostState : state.machine.user.payload.ghost=false := by
    change bM.user.payload.ghost=false
    dsimp only [bM]
    rw [RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost]
    exact initialGhost
  have shallowState : state.machine.user.payload.validation=.Shallow := by
    change bM.user.payload.validation=.Shallow
    dsimp only [bM]
    rw [RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow]
    exact initialShallow
  have rootFree : postTracker.global.protectedTags.contains rootTag=false := by
    rw [StackPopRelease.end_call_contains]
    split
    · rfl
    · exact heldFree
  have childFree : postTracker.global.protectedTags.contains tag=false := by
    rw [StackPopRelease.end_call_contains]
    simp [bf,FrameState.addProtector]
  have uncheckedEntered : (config.terminators.getControl initialMachine.user).checkedArithmetic=false := by
    change (config.terminators.getControl rawMachine.user).checkedArithmetic=false
    rw [RootZeroInvocationState.raw_control]
    exact unchecked
  have noGcEntered : (config.terminators.getControl initialMachine.user).gcInterval=0 := by
    change (config.terminators.getControl rawMachine.user).gcInterval=0
    rw [RootZeroInvocationState.raw_control]
    exact noGc
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have innerFields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨outer,outerAccess,outerArithmetic,_⟩ := fields.canonicalCopy
  obtain ⟨inner,innerAccess,innerArithmetic,_⟩ := innerFields.canonicalCopy
  have outerWidth : outer.pointers.arithmetic=⟨Size.ofBytes 8⟩ := outerArithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () (remaining+1) span)
  have innerWidth : inner.pointers.arithmetic=⟨Size.ofBytes 8⟩ := innerArithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () remaining span)
  have outerRuntime : outer.access.runtime=PreparedReflection.actual.runtime.target :=
    (congrArg (fun access => access.runtime) outerAccess).symm.trans (CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span)
  have innerRuntime : inner.access.runtime=PreparedReflection.actual.runtime.target :=
    (congrArg (fun access => access.runtime) innerAccess).symm.trans (CanonicalConfigFacts.actual_access_runtime options () remaining span)
  have endpoint : (allocRange place.mplace.ptr.offset (Size.ofBytes 1)).endExclusive=.ok (Size.ofBytes (base+1)) := by
    rw [pointer]
    have added := size_add_ok (Size.ofBytes base) (Size.ofBytes 1) (by simpa only [Size.ofBytes,UInt64.toNat_one] using fits)
    simp only [Pointer.new,allocRange,AllocRange.endExclusive,AllocRange.end,added,Except.mapError]
    rfl
  have maskValid : InitMaskCopy.WellFormed slotAllocation.initializationMask := by rw [protectedMask];trivial
  obtain ⟨result,trace,terminal,safe,props⟩ := RootZeroComplete.complete outer inner options remaining span innerAccess innerWidth
    (by rw [innerRuntime];rfl) (by rw [innerRuntime,outerRuntime]) limits validityFuel debug validityEq
    frame initialMachine bM rfl uncheckedEntered noGcEntered fixed heldTracker bf rfl frameBorrow releasedMemory profile
    {thread with topUserRelevantFrame:=some 0} activeEntered state rfl (frameBody.trans raw.body) (frameIdentity.trans raw.identity)
    (frameCallee.trans raw.callee) frameLocation frameSize source (congrArg (fun row=>row.value) slot3)
    (congrArg (fun row=>row.value) slot4) (congrArg (fun row=>row.value) slot5)
    (congrArg (fun row=>row.layout) slot4) (congrArg (fun row=>row.layout) slot5)
    (congrArg (fun row=>row.value) slot2) (congrArg (fun row=>row.layout) slot2)
    initialGhost initialShallow mode valid0 (frameRace.trans raw.noClocks)
    (frameContinuation.trans (RawRootInvocation.control before place race).2.2.1) allImmediate
    (by rw [frameVa];rfl) place id rootTag tag true base 1 newEntry postTracker
    (congrArg (fun row=>row.value) slot0) (congrArg (fun row=>row.layout) slot0) rfl layout outerWidth (by decide) (by decide)
    (by rw [addrState];exact cached) initialPresent protectedSize protectedMutable maskValid (by rw [outerRuntime];rfl)
    (by rw [protectedLen,protectedSize];rfl) (by rw [protectedMask,protectedSize];rfl) protectedProv race backendState rfl
    (by change state.machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [extrasState];exact extras)
    rootFree childFree protectedTree pointer aligned (by rw [outerRuntime];rfl) outerAccess ghostState shallowState
    (by rw [frameReturn];rfl) (Size.ofBytes (base+1)) endpoint
  exact ⟨Storage.withCurrent #[] frame initialMachine,CanonicalCopy.replaceAllocation state id entry.kind result,call',trace,terminal,safe⟩

#print axioms invoke
end DuplicatePrefix.WildcardGapRootZeroInvocation
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.WildcardGapRootZeroInvocation.invoke) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved genuine zero invocation dependency {dependency}"
