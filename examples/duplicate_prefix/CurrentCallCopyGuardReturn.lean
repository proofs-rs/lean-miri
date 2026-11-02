import duplicate_prefix.CurrentCallCopyGuard
import duplicate_prefix.CurrentCallCopyHelperExecution

/-! Opaque-ready composition of actual guard entry, physical copy and return. -/
namespace DuplicatePrefix.CurrentCallCopyGuardReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

variable (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
  (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
  (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
  (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
  (sourcePointer destinationPointer : Scalar Provenance) (n : UInt64)
  (ready : CopyRootEntry.Input options limits remaining span frames caller machine sourcePointer destinationPointer n)

def rootFrame : CompilerFrameContext.ActualFrame :=
  CopyRootGuardEntry.rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n ready

theorem rootValid : (18 : MIR.LocalId) < (rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n ready).locals.size := by
  simpa only [rootFrame,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,CopyUncachedCall.cachedCaller,
    LocalPlaces.cachePlaceLayout,Array.size_set] using ready.valid

def returnedFrame : CompilerFrameContext.ActualFrame :=
  {PtrMetadataExecution.writeFrame (rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n ready)
    18 .uninit (rootValid options limits remaining span frames caller machine sourcePointer destinationPointer n ready) with location := .mir ⟨9,0⟩}

theorem frame_projections :
    let result := returnedFrame options limits remaining span frames caller machine sourcePointer destinationPointer n ready
    result.body = caller.body ∧ result.bodyIdentity = caller.bodyIdentity ∧ result.functionInstance = caller.functionInstance ∧
    result.extra = caller.extra ∧ result.returnPlace = caller.returnPlace ∧ result.returnContinuation = caller.returnContinuation ∧
    result.vaList = caller.vaList ∧ result.localsIdentity = caller.localsIdentity ∧ result.trackCallerArg = caller.trackCallerArg ∧
    result.locals.size = caller.locals.size ∧ result.location = .mir ⟨9,0⟩ ∧
    result.locals[18]? = some ⟨.live (.immediate .uninit),some CopyHelperUnit.layout⟩ ∧
    (∀ index, index ≠ 18 → result.locals[index]? = caller.locals[index]?) := by
  dsimp only
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl,?_,?_⟩
  · simp only [returnedFrame,PtrMetadataExecution.writeFrame,rootFrame,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,
      CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set]
  · simp only [returnedFrame,PtrMetadataExecution.writeFrame,rootFrame,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,
      CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem?_set_self,Array.getElem_set_self]
  · intro index different
    simp only [returnedFrame,PtrMetadataExecution.writeFrame,rootFrame,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,
      CopyUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem?_set,Ne.symm different,different,ite_false]

/-- Returning the unit result changes only local 18, so any existing immediate
caller-local representation is preserved without an additional input gate. -/
theorem all_immediate (initial : CopyHelperCleanup.AllImmediate caller) :
    CopyHelperCleanup.AllImmediate (returnedFrame options limits remaining span frames caller machine sourcePointer destinationPointer n ready) := by
  let root := rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n ready
  have cached : CopyHelperCleanup.AllImmediate root :=
    CopyHelperCleanup.all_immediate_cache caller 18 CopyHelperUnit.layout ready.valid initial
  let bounded := rootValid options limits remaining span frames caller machine sourcePointer destinationPointer n ready
  exact CopyHelperCleanup.all_immediate_set root 18
    ⟨.live (.immediate .uninit),(root.locals[18]'bounded).layout⟩ bounded
    cached (by intro memory;simp)

private theorem replace_twice (state : RootState) (id : AllocId) (kind : MemoryKind MiriMemoryKind)
    (first second : Allocation Provenance BorrowTree) :
    CanonicalCopy.replaceAllocation (CanonicalCopy.replaceAllocation state id kind first) id kind second =
      CanonicalCopy.replaceAllocation state id kind second := by
  simp [CanonicalCopy.replaceAllocation,Array.filter_push,Array.filter_filter]

/-- The original ready packet stays opaque while the guard, copy and return
proofs consume its frame/cfg data. Access completion remains an internal lower
certificate rather than an original-call premise. -/
theorem run
    (statementFuel : Nat) (statementEq : limits.validation = statementFuel+1)
    (mode : ready.tracker.retagMode = .Default)
    (id : AllocId) (tag : BorTag) (base offset sliceLen : UInt64) (kind : MemoryKind MiriMemoryKind)
    (allocation : Allocation Provenance BorrowTree)
    (positive : 0 < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ allocation.byteSize.bytes.toNat)
    (copyBounds : n.toNat+n.toNat ≤ sliceLen.toNat)
    (storage : allocation.len = allocation.byteSize.bytes.toNat)
    (maskValid : InitMaskCopy.WellFormed allocation.initializationMask)
    (maskLen : allocation.initializationMask.len = allocation.byteSize)
    (initialized : InitMaskCopy.InitializedOn allocation.initializationMask (Size.ofBytes offset) (Size.ofBytes (offset+n)))
    (valid : S02SameDestinationUninitProvenanceInput.DirectInput allocation.provenanceMap allocation.len)
    (storageFits : allocation.len+64 < 18446744073709551616)
    (mutable : allocation.mutability = .Mut)
    (readReady : CurrentCallBoolProtection.WindowReady machine id offset.toNat n.toNat)
    (writeReady : CurrentCallBoolProtection.WindowReady machine id (offset+n).toNat n.toNat)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,⟨kind,allocation⟩))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (readCompleted : (allocation.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes n)
      .Read ready.tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (sequentialWriteCompleted : ((allocation.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes n)
      .Read ready.tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange (.concrete tag)
      (Size.ofBytes (offset+n)) (Size.ofBytes n) .Write ready.tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (bounded : n ≤ (config options (remaining+1) span).projection.maxSizeOfVal.bytes)
    (sourceValue : sourcePointer = Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))))
    (destinationValue : destinationPointer = Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+(offset+n))))) :
    let readAccess := allocation.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes n)
      .Read ready.tracker.global.protectedTags .VisitChildrenOfAccessed
    let writeAccess := readAccess.tree.performBorrowAccessRange (.concrete tag) (Size.ofBytes (offset+n)) (Size.ofBytes n)
      .Write ready.tracker.global.protectedTags .VisitChildrenOfAccessed
    ∃ guardMachine copied finalMachine,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent frames caller machine)
        (Storage.withCurrent frames (returnedFrame options limits remaining span frames caller machine sourcePointer destinationPointer n ready) finalMachine) ∧
      LanguageGuardReturn.Preserves options remaining span machine guardMachine ∧
      finalMachine.memory.live.find? (fun row => row.1 == id) = some (id,⟨kind,copied⟩) ∧
      copied.byteSize = allocation.byteSize ∧ copied.len = allocation.len ∧ copied.extra = writeAccess.tree ∧
      AllocationCopy.snapshot copied = (AllocationCopy.snapshot allocation).extract 0 (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract offset.toNat (offset+n).toNat ++
        (AllocationCopy.snapshot allocation).extract (offset+n+n).toNat allocation.len ∧
      S02SameDestinationAcceptedCopyPhysical.Physical copied ∧
      finalMachine.memory = (CanonicalCopy.replaceAllocation (Storage.withCurrent frames caller machine) id kind copied).machine.memory ∧
      finalMachine.borrowTracker = some ready.tracker ∧
      finalMachine.user = (CopyHelperClock.advance options remaining span
        (CopyHelperClock.advance options remaining span (CopyHelperClock.advance options remaining span guardMachine))).user ∧
      finalMachine.dataRace = machine.dataRace ∧ finalMachine.threads.fixedScheduling = machine.threads.fixedScheduling ∧
      (∃ finalThread, finalMachine.threads.activeThread? = some finalThread) := by
  let root := rootFrame options limits remaining span frames caller machine sourcePointer destinationPointer n ready
  obtain ⟨guardMachine,guardTrace,preserved,guardActor⟩ := CurrentCallCopyGuard.run options limits remaining span frames caller machine sourcePointer destinationPointer n ready statementFuel statementEq mode
  have metadata := CurrentCallCopyGuard.returned_metadata options limits remaining span frames caller machine sourcePointer destinationPointer n ready
  have rows := CurrentCallCopyGuard.returned_locals options limits remaining span frames caller machine sourcePointer destinationPointer n ready
  have helperAll := CurrentCallCopyGuard.returned_all_immediate options limits remaining span frames caller machine sourcePointer destinationPointer n ready
  generalize helperEq : CurrentCallCopyGuard.returnedCopy options limits remaining span frames caller machine sourcePointer destinationPointer n ready = helper at guardTrace metadata rows helperAll
  have helperLive : guardMachine.memory.live.find? (fun row => row.1 == id) = some (id,⟨kind,allocation⟩) := by rw [preserved.memory];exact live
  have helperCached : guardMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by rw [preserved.addresses];exact cached
  have helperTracked : guardMachine.borrowTracker = some ready.tracker := preserved.tracker.trans ready.tracked
  have helperRace : guardMachine.dataRace = none := preserved.race.trans ready.noRace
  have helperBackend : guardMachine.user.payload.payload.user.backend = .none := preserved.backend.trans ready.backend
  have helperGhost : guardMachine.user.payload.ghost = false := preserved.ghost.trans ready.ghost
  have helperShallow : guardMachine.user.payload.validation = .Shallow := preserved.validation.trans ready.shallow
  have helperUnchecked : ((config options (remaining+1) span).terminators.getControl guardMachine.user).checkedArithmetic = false := preserved.unchecked.trans ready.unchecked
  have helperNoGc : ((config options (remaining+1) span).terminators.getControl guardMachine.user).gcInterval = 0 := preserved.noGc.trans ready.noGc
  have helperFixed : guardMachine.threads.fixedScheduling = true := preserved.fixed.trans ready.fixed
  have readReadyNow := readReady.transport preserved.extras
  have writeReadyNow := writeReady.transport preserved.extras
  have helperSize := metadata.2.2.2.2.1
  have helperValid (index : Fin 17) : index.val < helper.locals.size := by rw [helperSize];exact index.isLt
  have helperCell (index : Fin 17) (row : LocalState Provenance LocalLayout)
      (known : (#[⟨.live (.immediate .uninit),none⟩,
        ⟨.live (.immediate (.scalar sourcePointer)),some CopyCompilerFacts.sourcePointerLayout⟩,
        ⟨.live (.immediate (.scalar destinationPointer)),some CopyCompilerFacts.destPointerLayout⟩,
        ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩,
        ⟨.live (.immediate .uninit),none⟩,
        ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩] ++
        Array.replicate 11 ⟨.dead,none⟩)[index.val]? = some row) : helper.locals[index.val]'(helperValid index) = row :=
    by
      have fetched : helper.locals[index.val]? = some row := by
        rw [rows]
        exact known
      exact Option.some.inj ((Array.getElem?_eq_getElem (helperValid index)).symm.trans fetched)
  have c0 := helperCell ⟨0,by decide⟩ ⟨.live (.immediate .uninit),none⟩ rfl
  have c1 := helperCell ⟨1,by decide⟩ ⟨.live (.immediate (.scalar sourcePointer)),some CopyCompilerFacts.sourcePointerLayout⟩ rfl
  have c2 := helperCell ⟨2,by decide⟩ ⟨.live (.immediate (.scalar destinationPointer)),some CopyCompilerFacts.destPointerLayout⟩ rfl
  have c3 := helperCell ⟨3,by decide⟩ ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 n)))),some RootCompilerFacts.usizeLayout⟩ rfl
  have c4 := helperCell ⟨4,by decide⟩ ⟨.live (.immediate .uninit),none⟩ rfl
  have c5 := helperCell ⟨5,by decide⟩ ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ rfl
  have c14 := helperCell ⟨14,by decide⟩ ⟨.dead,none⟩ rfl
  have c15 := helperCell ⟨15,by decide⟩ ⟨.dead,none⟩ rfl
  have c16 := helperCell ⟨16,by decide⟩ ⟨.dead,none⟩ rfl
  have callerValid : (18 : MIR.LocalId) < root.locals.size := rootValid options limits remaining span frames caller machine sourcePointer destinationPointer n ready
  have callerLive : root.locals[18].value = .live (.immediate ready.old) := by
    simpa only [root,rootFrame,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,CopyUncachedCall.cachedCaller,
      LocalPlaces.cachePlaceLayout,Array.getElem_set_self] using ready.live
  have callerCached : root.locals[18].layout = some CopyHelperUnit.layout := by
    simp only [root,rootFrame,CopyRootGuardEntry.rootFrame,CopyRootEntry.cachedCaller,CopyUncachedCall.cachedCaller,
      LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  obtain ⟨helperThread,helperActive⟩ := guardActor
  obtain ⟨copied,finalMachine,copyTrace,copiedLive,copiedSize,copiedLen,copiedTree,copiedBytes,copiedPhysical,finalMemory,finalTracker,finalUser,finalRace,finalFixed,finalActor⟩ :=
    CurrentCallCopyHelperExecution.returns_to_caller options limits remaining span ready.source ready.debug ready.fuel ready.validationFuel frames root helper guardMachine
      metadata.1 metadata.2.1 metadata.2.2.1 metadata.2.2.2.1 helperSize ready.tracker id tag base offset sliceLen n kind allocation
      positive sliceBounds copyBounds storage maskValid maskLen initialized valid storageFits mutable
      helperRace helperBackend helperTracked readReadyNow writeReadyNow helperLive helperCached readCompleted sequentialWriteCompleted bounded
      (by rw [c1,sourceValue]) (by rw [c2,destinationValue]) (by rw [c3] <;> rfl)
      (by rw [c1] <;> rfl) (by rw [c2] <;> rfl) (by rw [c3] <;> rfl)
      (by rw [c4] <;> rfl) (by rw [c4] <;> rfl) (by rw [c5] <;> rfl) (by rw [c5] <;> rfl)
      (by rw [c14] <;> rfl) (by rw [c14] <;> rfl) (by rw [c15] <;> rfl) (by rw [c15] <;> rfl)
      (by rw [c16] <;> rfl) (by rw [c16] <;> rfl)
      helperAll
      metadata.2.2.2.2.2.2.2.2.1 mode helperUnchecked helperNoGc helperFixed helperGhost helperShallow
      (by rw [c0] <;> rfl) (by rw [c0] <;> rfl) metadata.2.2.2.2.2.2.2.1
      {} metadata.2.2.2.2.2.2.2.2.2 rfl helperThread helperActive 18 callerValid ready.old callerLive callerCached ready.noClocks
      (by rw [metadata.2.2.2.2.2.1] <;> rfl) 9 .Continue metadata.2.2.2.2.2.2.1
  have originalMemory : finalMachine.memory = (CanonicalCopy.replaceAllocation (Storage.withCurrent frames caller machine) id kind copied).machine.memory := by
    rw [finalMemory]
    rw [replace_twice,replace_twice]
    change (CanonicalCopy.replaceAllocation (Storage.withCurrent frames caller guardMachine) id kind copied).machine.memory = _
    simp only [CanonicalCopy.replaceAllocation,Storage.withCurrent,preserved.memory]
  refine ⟨guardMachine,copied,finalMachine,SuccessfulTrace.append guardTrace copyTrace,preserved,copiedLive,copiedSize,copiedLen,copiedTree,copiedBytes,copiedPhysical,
    originalMemory,finalTracker,finalUser,finalRace.trans preserved.race,finalFixed.trans preserved.fixed,finalActor⟩

end
end DuplicatePrefix.CurrentCallCopyGuardReturn
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallCopyGuardReturn." || name.toString.startsWith "_private.duplicate_prefix.CurrentCallCopyGuardReturn." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current copy guard return dependency {dependency}"
