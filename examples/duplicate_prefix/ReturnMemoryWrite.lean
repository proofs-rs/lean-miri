import duplicate_prefix.ReturnProtection
import duplicate_prefix.PhysicalMachineWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.ReturnMemoryWrite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext

theorem actual_uninit_eq (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (context : PhysicalMachineWrite.Context) (access : (config options remaining span).access = context.access)
    (place : MPlaceTy Provenance) (state : RootState)
    (ghost : state.machine.user.payload.ghost = false) :
    (config options remaining span).retag.writeUninit place state =
      PlaceMachine.writeMemory context.access (fun _ => false) .uninit place state := by
  rw [ctx.construction]
  change (do let activeAccess ← ValidityMachine.scopedAccess (config options remaining span).access
             PlaceMachine.writeMemory activeAccess (fun _ => false) .uninit place) state = _
  unfold ValidityMachine.scopedAccess ValidityMachine.validationInProgress
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, ghost, pure, EStateM.pure]
  rw [access]
  rfl


theorem protected_uninit (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (state : RootState) (place : MPlaceTy Provenance) (id : AllocId) (root child : BorTag)
    (written : Bool) (base count : UInt64) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (tracker : MachineHooks.BorrowState)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes count)
    (mutable : entry.allocation.mutability = .Mut)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (provenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (enabled : state.machine.borrowTracker = some tracker)
    (extras : state.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (rootFree : tracker.global.protectedTags.contains root = false)
    (childHeld : tracker.global.protectedTags.contains child = true)
    (distinct : root ≠ child)
    (initialTree : entry.allocation.extra = PhysicalMachineWrite.slotTree root child count written)
    (unsized : place.layout.layout.backendRepr.isUnsized = false)
    (placeSize : place.layout.layout.size = Size.ofBytes count)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id child)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (ghost : state.machine.user.payload.ghost = false) :
    ∃ updated, (config options remaining span).retag.writeUninit place state =
      .ok () (CanonicalCopy.replaceAllocation state id entry.kind updated) ∧
      updated.extra = PhysicalMachineWrite.slotTree root child count true ∧ updated.byteSize = entry.allocation.byteSize ∧ updated.len = entry.allocation.len ∧
      updated.initializationMask = InitMask.new entry.allocation.byteSize false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot entry.allocation ∧
      updated.mutability = entry.allocation.mutability := by
  have fields := actual_fields options () remaining span
  obtain ⟨context, access, arithmetic, atomic⟩ := fields.canonicalCopy
  have width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩ :=
    arithmetic.symm.trans (actual_arithmetic options () remaining span)
  have runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8 := by
    rw [← access, actual_access_runtime]
    rfl
  obtain ⟨updated, action, tree, byteSize, length, mask, prov, snapshot, mutableEq⟩ :=
    PhysicalMachineWrite.uninit_protected_slot context state place id root child written base count entry tracker
      width positive signedFits cached present size mutable storage maskLength provenance noClocks noBackend enabled extras
      rootFree childHeld distinct initialTree unsized placeSize pointer aligned runtimeSize
  refine ⟨updated, ?_, tree, byteSize, length, mask, prov, snapshot, mutableEq⟩
  rw [actual_uninit_eq options remaining span ctx context access place state ghost]
  exact action

end DuplicatePrefix.ReturnMemoryWrite

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ReturnMemoryWrite.actual_uninit_eq,
      ``DuplicatePrefix.ReturnMemoryWrite.protected_uninit] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved actual return memory write dependency {dependency}"
