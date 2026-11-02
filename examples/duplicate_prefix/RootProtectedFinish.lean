import duplicate_prefix.ActualReturnProtection
import duplicate_prefix.RootEntryFinish
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
namespace DuplicatePrefix.RootProtectedFinish
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
theorem protect_and_finish
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
    (noClocks : frame.extra.dataRace = none) :
    let child := tracker.global.nextPointerTag
    let borrowed := ReturnProtection.borrowedState frames frame borrowFrame machine tracker fresh id entry
      (PhysicalMachineWrite.slotTree rootTag child 1 false)
    ∃ updated,
      (do
        (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
        RootEntryFinish.finish (ExecutionMachine.callHooks (config options remaining span) limits))
        (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        (CallEntryFacts.doneRootFrame {registeredFrame frame borrowFrame id child with location := .unwinding ⟨559⟩})
        (CanonicalCopy.replaceAllocation borrowed id entry.kind updated).machine) ∧
      updated.extra = PhysicalMachineWrite.slotTree rootTag child 1 true ∧
      updated.byteSize = Size.ofBytes 1 ∧ updated.len = 1 ∧
      updated.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot entry.allocation ∧
      updated.mutability = .Mut := by
  obtain ⟨updated, protect, properties⟩ := ActualReturnProtection.protect_bool options limits remaining span ctx place layout
    frames frame borrowFrame machine tracker enabled frameBorrow fresh id entry base rootTag pointer aligned cached root size present
    race distinct unprotected mutable storage maskLength provenance noBackend extras ghost
  refine ⟨updated, ?_, properties⟩
  simp only [bind, EStateM.bind]
  rw [protect]
  simp only [EStateM.bind]
  let protectedFrame := registeredFrame frame borrowFrame id tracker.global.nextPointerTag
  let borrowed := ReturnProtection.borrowedState frames frame borrowFrame machine tracker fresh id entry
    (PhysicalMachineWrite.slotTree rootTag tracker.global.nextPointerTag 1 false)
  let protectedState := CanonicalCopy.replaceAllocation borrowed id entry.kind updated
  have finish := RootEntryFinish.actual_finish options limits remaining span frames protectedFrame protectedState.machine
    body localSize dead0 dead6 dead13 dead14 noClocks
  exact finish
end DuplicatePrefix.RootProtectedFinish
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RootProtectedFinish.protect_and_finish) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved protected root finish dependency {dependency}"
