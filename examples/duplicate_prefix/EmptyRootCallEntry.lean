import duplicate_prefix.EmptyRootContinuation
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace DuplicatePrefix.EmptyRootCallEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
theorem actual_entry
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options (remaining+1) span)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (rootFrame : RootFrameData.RootFrame) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : rootFrame.frame.extra.borrowTracker = some borrowFrame)
    (initialFresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (fresh : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag initialFresh).value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base : UInt64) (rootTag : BorTag)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id rootTag)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (root : entry.allocation.extra = BorrowTree.new rootTag (Size.ofBytes 1))
    (size : entry.allocation.byteSize = Size.ofBytes 1)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none)
    (distinct : rootTag ≠ TypedRetagEmpty.successorTag tracker.global.nextPointerTag initialFresh)
    (unprotected : tracker.global.protectedTags.contains rootTag = false)
    (mutable : entry.allocation.mutability = .Mut)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (provenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (ghost : machine.user.payload.ghost = false)
    (dead0 : (rootFrame.frame.locals[0]'(rootFrame.valid ⟨0,by decide⟩)).value = .dead)
    (dead6 : (rootFrame.frame.locals[6]'(rootFrame.valid ⟨6,by decide⟩)).value = .dead)
    (dead13 : (rootFrame.frame.locals[13]'(rootFrame.valid ⟨13,by decide⟩)).value = .dead)
    (dead14 : (rootFrame.frame.locals[14]'(rootFrame.valid ⟨14,by decide⟩)).value = .dead)
    (address n : UInt64) (nonzero : address ≠ 0)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (precise : options.retag.preciseInteriorMut = false) (implicitWrites : options.retag.implicitWrites = false)
    (debug : options.place.debugAssertions = false) (dynamicFuel validityFuel : Nat)
    (dynamicEq : options.place.dynamicFuel = dynamicFuel+1) (validityEq : options.limits.validation = validityFuel+1)
    (shallow : machine.user.payload.validation = .Shallow)
    (metadata : machine.user.payload.payload.user.types.metadata = PreparedReflection.actual.runtime)
    (notConstructed : machine.user.payload.payload.user.types.entries.any (·.value.ty == 4) = false)
    (dead1 : (rootFrame.frame.locals[1]'(rootFrame.valid EmptyRootArguments.i1)).value = .dead)
    (cache1 : (rootFrame.frame.locals[1]'(rootFrame.valid EmptyRootArguments.i1)).layout = none)
    (dead2 : (rootFrame.frame.locals[2]'(rootFrame.valid EmptyRootArguments.i2)).value = .dead)
    (cache2 : (rootFrame.frame.locals[2]'(rootFrame.valid EmptyRootArguments.i2)).layout = none)
    (initial : RootState) (thread : Miri.Concurrency.ThreadRecord)
    (active : initial.machine.threads.activeThread? = some thread)
    (noCache : thread.topUserRelevantFrame = none)
    (rawEq : CallEntryFacts.rawPushedState initial.stack.frames initial.machine (.memory place) =
      Storage.withCurrent frames rootFrame.frame machine)
    (preamble : rootFrame.frame.location = .unwinding ⟨559⟩)
    (trackNone : rootFrame.frame.trackCallerArg = none) :
    let argsFrame := EmptyRootArguments.result rootFrame address n
    let argsMachine := allocatedMachine machine tracker initialFresh
    let next := allocatedTracker tracker initialFresh
    let changed := {argsFrame.frame with location := FrameLocation.unwinding ⟨601⟩}
    let borrowed := ReturnProtection.borrowedState frames changed borrowFrame argsMachine next fresh id entry
      (PhysicalMachineWrite.slotTree rootTag next.global.nextPointerTag 1 false)
    ∃ updated,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (EmptyRootArguments.first address), .Copy (EmptyRootArguments.second n)] false (.memory place) (.stop true) initial =
      .ok () (Storage.withCurrent frames
        (CallEntryFacts.doneRootFrame {registeredFrame changed borrowFrame id next.global.nextPointerTag with location := .unwinding ⟨559⟩})
        (CanonicalCopy.replaceAllocation borrowed id entry.kind updated).machine) ∧
      updated.extra = PhysicalMachineWrite.slotTree rootTag next.global.nextPointerTag 1 true ∧
      updated.byteSize = Size.ofBytes 1 ∧ updated.len = 1 ∧
      updated.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot entry.allocation ∧
      updated.mutability = .Mut := by
  obtain ⟨updated, cont, props⟩ := EmptyRootContinuation.succeeds options limits remaining span ctx place layout frames rootFrame borrowFrame machine tracker
    enabled frameBorrow initialFresh fresh id entry base rootTag pointer aligned cached root size present race distinct unprotected mutable storage maskLength
    provenance noBackend extras ghost dead0 dead6 dead13 dead14 address n nonzero cmp precise implicitWrites debug dynamicFuel validityFuel
    dynamicEq validityEq shallow metadata notConstructed dead1 cache1 dead2 cache2
  have arguments := EmptyRootArgumentScope.arguments_in_scope options limits remaining span cmp precise implicitWrites debug
    dynamicFuel validityFuel dynamicEq validityEq frames rootFrame machine address n nonzero dead1 cache1 dead2 cache2
    ghost shallow tracker enabled initialFresh metadata notConstructed
  have push := CallEntryFacts.actual_call_hooks_push_raw options () (remaining+1) span limits debug initial (.memory place) thread active noCache
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span frames rootFrame.frame machine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span frames rootFrame.frame rootFrame.frame machine
  have unchanged : {rootFrame.frame with trackCallerArg := none} = rootFrame.frame := by
    rw [← trackNone]
  unfold EmptyRootContinuation.continuation at cont
  simp only [bind, EStateM.bind] at cont
  rw [arguments] at cont
  simp only [EStateM.bind] at cont
  refine ⟨updated, ?_, props⟩
  rw [RootCallCore.actual_entry_eq]
  unfold RootCallCore.core
  simp only [bind, EStateM.bind]
  unfold CallEntryFacts.config at push
  rw [push, rawEq]
  simp only [EStateM.bind]
  rw [getFrame]
  simp only [EStateM.bind, preamble, pure, EStateM.pure]
  simp only [preamble] at unchanged
  rw [unchanged, setFrame]
  simp only [EStateM.bind]
  rw [arguments]
  simp only [EStateM.bind]
  exact cont
end DuplicatePrefix.EmptyRootCallEntry
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.EmptyRootCallEntry.actual_entry) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved actual root entry dependency {dependency}"
