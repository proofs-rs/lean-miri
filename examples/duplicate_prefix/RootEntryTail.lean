import duplicate_prefix.RootProtectedFinish
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace DuplicatePrefix.RootEntryTail
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
noncomputable def tail (h : RootCallCore.RootHooks) (place : MPlaceTy Provenance) : MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  RootCallCore.spanAt h (← h.localSpan RootBody.reflected.body.body 0)
  unless ← h.checkArgumentCompat () RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  h.protectArgument () place
  RootEntryFinish.finish h
theorem actual_tail
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options remaining span)
    (place : MPlaceTy Provenance) (layout : place.layout = RootCompilerFacts.boolLayout)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base : UInt64) (rootTag : BorTag)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id rootTag)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (root : entry.allocation.extra = BorrowTree.new rootTag (Size.ofBytes 1))
    (size : entry.allocation.byteSize = Size.ofBytes 1)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none)
    (distinct : rootTag ≠ tracker.global.nextPointerTag)
    (unprotected : tracker.global.protectedTags.contains rootTag = false)
    (mutable : entry.allocation.mutability = .Mut)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (provenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (ghost : machine.user.payload.ghost = false)
    (body : frame.body = RootBody.reflected.body.body) (localSize : frame.locals.size = 25)
    (dead0 : (frame.locals[0]'(by omega)).value = .dead)
    (dead6 : (frame.locals[6]'(by omega)).value = .dead)
    (dead13 : (frame.locals[13]'(by omega)).value = .dead)
    (dead14 : (frame.locals[14]'(by omega)).value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    let child := tracker.global.nextPointerTag
    let changed := {frame with location := FrameLocation.unwinding ⟨601⟩}
    let borrowed := ReturnProtection.borrowedState frames changed borrowFrame machine tracker fresh id entry
      (PhysicalMachineWrite.slotTree rootTag child 1 false)
    ∃ updated,
      tail (ExecutionMachine.callHooks (config options remaining span) limits) place
        (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        (CallEntryFacts.doneRootFrame {registeredFrame changed borrowFrame id child with location := .unwinding ⟨559⟩})
        (CanonicalCopy.replaceAllocation borrowed id entry.kind updated).machine) ∧
      updated.extra = PhysicalMachineWrite.slotTree rootTag child 1 true ∧
      updated.byteSize = Size.ofBytes 1 ∧ updated.len = 1 ∧
      updated.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot entry.allocation ∧
      updated.mutability = .Mut := by
  let changed := {frame with location := FrameLocation.unwinding ⟨601⟩}
  obtain ⟨updated, protect, properties⟩ := RootProtectedFinish.protect_and_finish options limits remaining span ctx place layout
    frames changed borrowFrame machine tracker enabled frameBorrow fresh id entry base rootTag pointer aligned cached root size present
    race distinct unprotected mutable storage maskLength provenance noBackend extras ghost body localSize dead0 dead6 dead13 dead14 noClocks
  refine ⟨updated, ?_, properties⟩
  have localSpan := CallEntryLocals.root_span0 options limits remaining span frames frame machine body identity callee
  have getFrame := CallEntryLocals.get_frame options limits remaining span frames frame machine
  have setFrame := CallEntryLocals.set_frame options limits remaining span frames frame changed machine
  have compat : (ExecutionMachine.callHooks (config options remaining span) limits).checkArgumentCompat ()
      RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret (Storage.withCurrent frames changed machine) =
      .ok true (Storage.withCurrent frames changed machine) := by
    change (config options remaining span).calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [(actual_fields options () remaining span).callCompiler]
    exact CallEntryFacts.root_return_argument_compat _ options.compatibilityBudget _
  unfold tail RootCallCore.spanAt
  simp only [bind, EStateM.bind]
  rw [localSpan]
  simp only [EStateM.bind]
  rw [getFrame]
  simp only [EStateM.bind]
  dsimp only [changed] at setFrame
  rw [setFrame]
  simp only [EStateM.bind]
  dsimp only [changed] at compat
  rw [compat]
  simp only [EStateM.bind, Bool.not_true, ite_false, pure, EStateM.pure]
  exact protect
end DuplicatePrefix.RootEntryTail
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RootEntryTail.actual_tail) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved root entry tail dependency {dependency}"
