import duplicate_prefix.CurrentCallOrdinaryInput
import duplicate_prefix.CurrentCallConversionSourceFrame
import duplicate_prefix.CurrentCallPostEntryCheckpoint

/-! Source resources at the actual post-conversion copy phase. The source
constructor and converter are reused; this adapter only assembles their current
logical and physical resources for the common continuation. -/
namespace DuplicatePrefix.CurrentCallConversionSourceCheckpoint
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallLazySourceResources CurrentCallOrdinaryInput CurrentCallPostEntryCheckpoint
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

private theorem present_of_live (post : Before) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : post.memory.live.find? (fun row => row.1 == id) = some (id, entry)) :
    Present (ActualWorld post) id entry.allocation := by
  simp only [Present, ActualWorld, Array.toList_map]
  exact List.mem_map.mpr ⟨(id, entry),
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live), rfl⟩

/-- Both logical source and copy readiness refer to the same actual copied
allocation. The converted provenance consistency is supplied by the finite
converter's checked `wellFormed` field, not by an admission success test. -/
theorem at_post (global : GlobalState) (frame : FrameState) (id : AllocId) (root : BorTag)
    (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit)
    (attributes : GlobalAllocationAttributes.Attributes source converted)
    (offset len : UInt64) (physical : Physical source offset len true)
    (wellFormed : ProvenanceCopy.WellFormed converted.provenanceMap converted.len)
    (storageRoom : source.len + 64 < 2^64)
    (rootCached : global.rootTag? id = some root)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (stage : Stage global frame id root source.byteSize.bytes offset len room)
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808)
    (base : UInt64) (baseRoom : base.toNat + source.byteSize.bytes.toNat < 2^64)
    (nonnull : base + offset ≠ 0)
    (post : Before) (next : MachineHooks.BorrowState)
    (actualRoot : next.global.rootTag? id = some root)
    (flags : next.global.protectedTags = stage.output.global.protectedTags)
    (counter : stage.output.global.nextPointerTag.value.toNat ≤ next.global.nextPointerTag.value.toNat)
    (live : post.memory.live.find? (fun row => row.1 == id) =
      some (id, ⟨.machine .global, converted.mapExtra (fun _ => stage.output.child.tree)⟩))
    (cached : post.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (extras : post.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none, #[]⟩)) (data : Identities) :
    ∃ current : Source post next offset.toNat len,
      CopyReady current ∧ current.role.backing.id = id ∧
      current.role.family.value = Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset)) ∧
      current.role.backing.allocation = converted.mapExtra (fun _ => stage.output.child.tree) ∧
      current.grant = stage.child ∧ current.tag = global.nextPointerTag := by
  obtain ⟨qData, qOwner, Q, pointer, allocation, completion, runtime⟩ :=
    CurrentCallConversionSourceFrame.at_post global frame id root source converted attributes physical.1.1 rootCached
      offset len room stage physical.2.2.1 base post next actualRoot flags counter
      (present_of_live post id _ live) data
  have offsetEq : UInt64.ofNat offset.toNat = offset := UInt64.ofNat_toNat
  have storage : Q.allocation.len = Q.allocation.byteSize.bytes.toNat := by
    rw [allocation]
    change converted.len = converted.byteSize.bytes.toNat
    rw [attributes.storage, attributes.size]
    exact physical.1.1
  have nodeAt : Q.allocation.extra.nodes.get Q.pointer.grant = some stage.node := by
    rw [allocation, pointer]
    exact stage.nodeAt
  have activity : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra Q.pointer.grant .Write
      (UInt64.ofNat offset.toNat) (UInt64.ofNat offset.toNat + len) := by
    rw [allocation, pointer, offsetEq]
    exact stage.activity
  have binding : CandidateCallBindings.WindowBinding post Q.pointer.value id offset.toNat len.toNat := by
    rw [pointer]
    refine ⟨⟨.machine .global, converted.mapExtra (fun _ => stage.output.child.tree)⟩, base, live, cached, ?_, ?_, ?_, ?_, nonnull, rfl⟩
    · change converted.len = converted.byteSize.bytes.toNat
      rw [attributes.storage, attributes.size]
      exact physical.1.1
    · change base.toNat + converted.len < 2^64
      rw [attributes.storage, physical.1.1]
      exact baseRoom
    · change offset.toNat + len.toNat ≤ converted.len
      rw [attributes.storage, physical.1.1]
      exact physical.2.2.1
    · change (base + offset).toNat = base.toNat + offset.toNat
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by have bounds := physical.2.2.1; omega)]
  have distinct : Q.allocation.extra.roots.toList.Nodup := by
    rw [allocation]
    change stage.output.child.tree.roots.toList.Nodup
    rw [stage.roots]
    simp
  have nodes : Q.allocation.extra.nodes.size + 6 < 65536 := by
    rw [allocation]
    have bound := stage.growth
    change stage.output.child.tree.nodes.size + 6 < 65536
    omega
  let current := Source.ofUniform Q runtime distinct global.nextPointerTag
    (by rw [pointer]; rfl) stage.node nodeAt (stage.nodeTag.trans stage.tag) stage.hidden
    activity binding positive signedFits nodes
  have convertedPhysical : OrdinaryPhysicalValidity.MutU8Slice Q.allocation offset len := by
    refine ⟨⟨storage, ?_, ?_, ?_⟩, positive, signedFits, ?_, ?_, ?_⟩
    · rw [allocation]
      change converted.initializationMask.len = converted.byteSize
      rw [attributes.mask, attributes.size]
      exact physical.1.2.2.1
    · rw [allocation]
      change InitMaskCopy.WellFormed converted.initializationMask
      rw [attributes.mask]
      exact physical.1.2.1
    · rw [allocation]
      exact wellFormed
    · rw [allocation]
      change offset.toNat + len.toNat ≤ converted.byteSize.bytes.toNat
      rw [attributes.size]
      exact physical.2.2.1
    · rw [allocation]
      change converted.mutability = .Mut
      rw [attributes.mutability]
      exact physical.2.1
    · intro byte lower upper
      rw [allocation]
      change OrdinaryPhysicalValidity.ByteInitialized converted.initializationMask byte
      rw [attributes.mask]
      exact physical.2.2.2 rfl byte lower upper
  have copyStorage : CurrentCallResourceEntrySourceStorage.Data Q.allocation (UInt64.ofNat offset.toNat) len := by
    rw [offsetEq]
    have formed := convertedPhysical.storage.provenance
    refine ⟨convertedPhysical.slice_storage, storage, ⟨ProvenanceCopy.WellFormed.pointerOrder formed, ProvenanceCopy.WellFormed.pointerBounds formed,
      ProvenanceCopy.WellFormed.fragmentsAvoidPointers formed, ?_⟩, convertedPhysical.writable, ?_⟩
    · have count := formed.fragment_count
      omega
    · rw [allocation]
      change converted.len + 64 < 2^64
      rw [attributes.storage]
      exact storageRoom
  refine ⟨current, ⟨copyStorage, ?_⟩, rfl, ?_, allocation, ?_, rfl⟩
  · exact ⟨#[], extras, by simp⟩
  · exact congrArg PointerInstance.value pointer
  · exact congrArg PointerInstance.grant pointer

end
end DuplicatePrefix.CurrentCallConversionSourceCheckpoint

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallConversionSourceCheckpoint.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved converted source checkpoint dependency {name}: {dependency}"
