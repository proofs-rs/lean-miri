import duplicate_prefix.ReturnMemoryWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.ActualReturnProtection
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver

theorem held_insert (tags : ProtectedTags) (tag : BorTag) : (tags.insert tag .StrongProtector).contains tag = true := by
  have absent : (tags.entries.filter (fun row => row.1 != tag)).find? (fun row => row.1 == tag) = none := by
    rw [Array.find?_filter]
    apply Array.find?_eq_none.mpr
    intro row member
    cases h : row.1 == tag with
    | false => simp
    | true => simp [beq_iff_eq.mp h]
  simp [ProtectedTags.contains, ProtectedTags.get, ProtectedTags.insert, Array.find?_push, absent]

theorem protect_bool
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
    (ghost : machine.user.payload.ghost = false) :
    let child := tracker.global.nextPointerTag
    let borrowed := ReturnProtection.borrowedState frames frame borrowFrame machine tracker fresh id entry
      (PhysicalMachineWrite.slotTree rootTag child 1 false)
    ∃ updated, (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames frame machine) =
      .ok () (CanonicalCopy.replaceAllocation borrowed id entry.kind updated) ∧
      updated.extra = PhysicalMachineWrite.slotTree rootTag child 1 true ∧
      updated.byteSize = Size.ofBytes 1 ∧ updated.len = 1 ∧
      updated.initializationMask = InitMask.new (Size.ofBytes 1) false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot entry.allocation ∧
      updated.mutability = .Mut := by
  let child := tracker.global.nextPointerTag
  let tree := PhysicalMachineWrite.slotTree rootTag child 1 false
  let borrowed := ReturnProtection.borrowedState frames frame borrowFrame machine tracker fresh id entry tree
  let changedEntry := {entry with allocation := entry.allocation.setExtra tree}
  let nextTracker := registeredTracker (allocatedTracker tracker fresh) child
  let changedPlace := TypedRetagGeneric.retaggedPlace place id child
  have postPresent : borrowed.machine.memory.live.find? (fun row => row.1 == id) = some (id,changedEntry) :=
    MemoryCopyBridge.live_lookup_replaced machine.memory id changedEntry
  have postRoot : nextTracker.global.protectedTags.contains rootTag = false := by
    change (tracker.global.protectedTags.insert child .StrongProtector).contains rootTag = false
    unfold ProtectedTags.contains
    rw [ProtectedTagsFacts.insert_preserves_other tracker.global.protectedTags rootTag child .StrongProtector distinct]
    exact unprotected
  have postHeld : nextTracker.global.protectedTags.contains child = true := held_insert tracker.global.protectedTags child
  have postPointer : changedPlace.mplace.ptr = Pointer.new (some (.concrete id child)) (Size.ofBytes base) := by
    unfold changedPlace TypedRetagGeneric.retaggedPlace
    rw [pointer]
    rfl
  have postSized : changedPlace.layout.layout.backendRepr.isUnsized = false := by
    change place.layout.layout.backendRepr.isUnsized = false
    rw [layout]
    decide +kernel
  have postSize : changedPlace.layout.layout.size = Size.ofBytes 1 := by
    change place.layout.layout.size = Size.ofBytes 1
    rw [layout]
    exact ActualRetagContext.bool_layout_exact.1
  obtain ⟨updated, write, treeEq, byteSize, length, mask, prov, snapshot, mutabilityEq⟩ :=
    ReturnMemoryWrite.protected_uninit options remaining span ctx borrowed changedPlace id rootTag child false base 1
      changedEntry nextTracker (by decide) (by decide) cached postPresent size mutable storage maskLength provenance race
      noBackend (by rfl) extras postRoot postHeld distinct (by rfl) postSized postSize postPointer aligned ghost
  have final := ReturnProtection.protect_bool_from_write options remaining span ctx limits.retag place layout frames frame borrowFrame
    machine tracker enabled frameBorrow fresh id entry base rootTag pointer cached root size present race distinct unprotected
    (CanonicalCopy.replaceAllocation borrowed id entry.kind updated) write
  refine ⟨updated, ?_, treeEq, byteSize.trans size, ?_, ?_, prov, snapshot, mutabilityEq.trans mutable⟩
  · rw [ReturnProtection.actual_call_protection]
    exact final
  · rw [length]
    change entry.allocation.len = 1
    rw [storage, size]
    rfl
  · rw [mask]
    change InitMask.new entry.allocation.byteSize false = _
    rw [size]

end DuplicatePrefix.ActualReturnProtection

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.ActualReturnProtection.protect_bool) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved complete actual return protection dependency {dependency}"
