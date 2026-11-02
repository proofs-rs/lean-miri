import duplicate_prefix.S05DiagnosticFnEntryContinuation
namespace DuplicatePrefix.S05DiagnosticFnEntryCall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts RootFrameData EmptyRootArguments ActualReferenceContext PositiveRootArguments S05DiagnosticFnEntryScope
open TypedBorrowSteps ReferenceBorrowDriver
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option linter.unusedSimpArgs false
/-- Internal composition of the diagnostic continuation with actual raw push.
The raw-push state equation is discharged by the physical invocation wrapper;
this theorem alone does not construct an initial caller or prove NoUB. -/
theorem actual_entry
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (parentTag : BorTag) (tracker : MachineHooks.BorrowState)
    (base n : UInt64) (nonzero : base ≠ 0)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (bounds : 2 ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (dead1 : (root.frame.locals[1]'(root.valid i1)).value = .dead)
    (cache1 : (root.frame.locals[1]'(root.valid i1)).layout = none)
    (dead2 : (root.frame.locals[2]'(root.valid i2)).value = .dead)
    (cache2 : (root.frame.locals[2]'(root.valid i2)).layout = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (borrowFrame : FrameState) (frameBorrow : root.frame.extra.borrowTracker = some borrowFrame)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : entry.allocation.extra = S05DiagnosticFnEntryRead.tree)
    (parentEq : parentTag = S05DiagnosticFnEntryRead.tag 6)
    (nextEq : tracker.global.nextPointerTag = S05DiagnosticFnEntryRead.tag 8)
    (protectedEq : tracker.global.protectedTags = ({} : ProtectedTags))
    (race : machine.dataRace = none)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (retagCtx : ActualRetagContext.Context options (remaining+1) span)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (slotId : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slotBase : UInt64) (slotRoot : BorTag)
    (slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase))
    (aligned : place.mplace.misaligned = none)
    (slotCached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩)
    (slotTree : slotEntry.allocation.extra = BorrowTree.new slotRoot (Size.ofBytes 1))
    (slotSize : slotEntry.allocation.byteSize = Size.ofBytes 1)
    (slotPresent : machine.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slotEntry))
    (separate : slotId ≠ id)
    (slotFresh : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value < 18446744073709551615)
    (slotDistinct : slotRoot ≠ TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh)
    (slotParentDistinct : slotRoot ≠ tracker.global.nextPointerTag)
    (slotFree : tracker.global.protectedTags.contains slotRoot = false)
    (mutable : slotEntry.allocation.mutability = .Mut)
    (storage : slotEntry.allocation.len = slotEntry.allocation.byteSize.bytes.toNat)
    (maskLength : slotEntry.allocation.initializationMask.len = slotEntry.allocation.byteSize)
    (provenance : slotEntry.allocation.provenanceMap = ProvenanceMap.new)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩))
    (dead0 : (root.frame.locals[0]'(root.valid ⟨0,by decide⟩)).value = .dead)
    (dead6 : (root.frame.locals[6]'(root.valid ⟨6,by decide⟩)).value = .dead)
    (dead13 : (root.frame.locals[13]'(root.valid ⟨13,by decide⟩)).value = .dead)
    (dead14 : (root.frame.locals[14]'(root.valid ⟨14,by decide⟩)).value = .dead)
    (initial : RootState) (thread : Miri.Concurrency.ThreadRecord)
    (active : initial.machine.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none)
    (rawEq : CallEntryFacts.rawPushedState initial.stack.frames initial.machine (.memory place) =
      Storage.withCurrent frames root.frame machine)
    (preamble : root.frame.location = .unwinding ⟨559⟩)
    (trackNone : root.frame.trackCallerArg = none) :
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base))) 2 ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base))) 2 ActualReferenceMetadata.reference).imm
    let argsFrame := RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted borrowFrame id tracker.global.nextPointerTag) n
    let argsMachine := resultMachine machine tracker fresh id entry parentTag
    let next : MachineHooks.BorrowState := ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,tracker.retagMode⟩
    let owned := borrowFrame.addProtector id tracker.global.nextPointerTag
    let changed := {argsFrame.frame with location := FrameLocation.unwinding ⟨601⟩}
    let borrowed := ReturnProtection.borrowedState frames changed owned argsMachine next slotFresh slotId slotEntry
      (PhysicalMachineWrite.slotTree slotRoot next.global.nextPointerTag 1 false)
    ∃ updated,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩,.Copy (second n)] false (.memory place) (.stop true) initial =
      .ok () (Storage.withCurrent frames
        (CallEntryFacts.doneRootFrame {registeredFrame changed owned slotId next.global.nextPointerTag with location := .unwinding ⟨559⟩})
        (CanonicalCopy.replaceAllocation borrowed slotId slotEntry.kind updated).machine) ∧
      updated.extra = PhysicalMachineWrite.slotTree slotRoot next.global.nextPointerTag 1 true ∧
      updated.byteSize = Size.ofBytes 1 ∧ updated.len = 1 ∧
      updated.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot slotEntry.allocation ∧
      updated.mutability = .Mut := by
  obtain ⟨updated,cont,props⟩ := S05DiagnosticFnEntryContinuation.succeeds options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id parentTag tracker base n nonzero entry bounds frames root machine
    dead1 cache1 dead2 cache2 ghost shallow cachedAddress present borrowFrame frameBorrow enabled fresh tree parentEq nextEq protectedEq race metadata notConstructed
    retagCtx place layout slotId slotEntry slotBase slotRoot slotPointer aligned slotCached slotTree slotSize slotPresent separate slotFresh slotDistinct slotParentDistinct
    slotFree mutable storage maskLength provenance noBackend extras dead0 dead6 dead13 dead14
  have arguments := S05DiagnosticFnEntryScope.scope options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id parentTag tracker base n nonzero entry bounds frames root machine
    dead1 cache1 dead2 cache2 ghost shallow cachedAddress present borrowFrame frameBorrow enabled fresh tree parentEq nextEq protectedEq race metadata notConstructed
  have push := CallEntryFacts.actual_call_hooks_push_raw options () (remaining+1) span limits debugOff initial (.memory place) thread active noCache
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span frames root.frame machine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span frames root.frame root.frame machine
  have unchanged : {root.frame with trackCallerArg := none} = root.frame := by rw [←trackNone]
  unfold S05DiagnosticFnEntryContinuation.continuation at cont
  simp only [bind,EStateM.bind] at cont
  rw [arguments] at cont
  simp only [EStateM.bind] at cont
  refine ⟨updated,?_,props⟩
  rw [RootCallCore.actual_entry_eq]
  unfold RootCallCore.core
  simp only [bind,EStateM.bind]
  unfold CallEntryFacts.config at push
  rw [push,rawEq]
  simp only [EStateM.bind]
  rw [getFrame]
  simp only [EStateM.bind,preamble,pure,EStateM.pure]
  simp only [preamble] at unchanged
  rw [unchanged,setFrame]
  simp only [EStateM.bind]
  rw [arguments]
  simp only [EStateM.bind]
  exact cont
end
end DuplicatePrefix.S05DiagnosticFnEntryCall

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticFnEntryCall." then
      for dependency in (←collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved diagnostic call dependency {dependency}"
