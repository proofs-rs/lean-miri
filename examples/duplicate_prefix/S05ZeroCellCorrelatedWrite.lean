import duplicate_prefix.S05ZeroCellTypedGeneratedPrefix
import duplicate_prefix.PhysicalMemoryWrite
import duplicate_prefix.CanonicalConfigFacts
import duplicate_prefix.S05PriorCellLayouts
import duplicate_prefix.OrdinaryPhysicalValidity

/-! Two-byte scalar specialization of the actual write pipeline.  The source
one/eight-byte helper is not widened; this derives two-byte encoding and uses
its already general allocation-write lemma. -/
namespace DuplicatePrefix.S05ZeroCellCorrelatedWrite
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
abbrev Context := CanonicalCopy.Context Unit Unit Unit Unit Unit Unit Unit Unit Machine.MinimalHost
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def sourceFor (tree : BorrowTree) : Allocation Provenance BorrowTree :=
  ((Allocation.fromBytes (Prov := Provenance) #[11,22] ⟨1⟩ .Mut).toOption.get (by decide)).withExtra tree

/-- Physical u8 value/storage facts of the actual two-byte write allocation.
This does not assert reference ownership or ordinary caller admissibility. -/
theorem sourceFor_physical (tree : BorrowTree) :
    OrdinaryPhysicalValidity.MutU8Slice (sourceFor tree) 0 2 := by
  constructor
  · constructor
    · rfl
    · rfl
    · cbv
    · change ProvenanceCopy.WellFormed (ProvenanceMap.new : ProvenanceMap Provenance) 2
      constructor <;> simp [ProvenanceMap.new, ProvenanceCopy.FragmentsAvoidPointers]
  · cbv
  · cbv
  · cbv
  · rfl
  · intro index lower upper
    rfl

def word : Scalar Provenance := Scalar.fromScalarInt (ScalarInt.ofUInt16 5643)

theorem write_scalar_same (target : TargetDataLayout) (little : target.endian = .little)
    (width : target.pointerWidth = .w64) (tree : BorrowTree) :
    Allocation.writeScalar target (allocRange Size.ZERO (Size.ofBytes 2)) word (sourceFor tree) =
      .ok () (sourceFor tree) := by
  have same : target = ⟨.little,.w64⟩ := by cases target; simp_all
  subst target
  cbv

open S05ZeroCellTypedGeneratedPrefix

def inputTree (stage : Bool) : BorrowTree := if stage then exposedV.tree else d.tree
def outputTree (stage : Bool) : BorrowTree := if stage then secondWrite.tree else firstWrite.tree

theorem word_abi (runtime : RuntimeTargetDataLayout) :
    immediate_abi (.scalar word) (localMemoryLayout PriorCellMetadata.u16Layout) runtime = .ok () := by
  with_unfolding_all rfl

theorem write_from_fields (context : Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (id : AllocId) (base : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (stage : Bool) (allocation : entry.allocation = sourceFor (inputTree stage))
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (runtimeWidth : context.access.runtime.base.pointerWidth = .w64)
    (little : context.access.runtime.base.endian = .little)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (enabled : state.machine.borrowTracker = some tracker)
    (protections : tracker.global.protectedTags = {})
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (layout : place.layout = PriorCellMetadata.u16Layout)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id (tag 1))) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8)
    (willValidate : MemoryOperandLayout → Bool := fun _ => false) :
    PlaceMachine.writeMemory context.access willValidate (.scalar word) place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
          (id,{entry with allocation := sourceFor (outputTree stage)}))}}} := by
  let config := context.access
  let tree := outputTree stage
  let afterEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {entry with allocation := sourceFor tree}
  let current := RetagEntry.updatedMemory state.machine.memory id entry tree
  have treeDone : (entry.allocation.extra.performBorrowAccessRange (.concrete (tag 1)) Size.ZERO (Size.ofBytes 2)
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    rw [allocation,protections]
    cases stage <;> cbv
  have treeEq : (entry.allocation.extra.performBorrowAccessRange (.concrete (tag 1)) Size.ZERO (Size.ofBytes 2)
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed).tree = tree := by
    rw [allocation,protections]
    cases stage <;> rfl
  have access : PlaceMachine.memoryAccess config true ⟨state.machine,none⟩ entry.allocation.extra id (.concrete (tag 1))
      (allocRange Size.ZERO (Size.ofBytes 2)) = ⟨⟨state.machine,none⟩,tree,.ok ()⟩ := by
    have fact := MemoryCopyBridge.source_memory_access_exact context.prepared context.image context.maximum context.fuel
      context.globalHooks context.pointers context.extras state.machine tracker entry.allocation.extra id (.concrete (tag 1))
      (allocRange Size.ZERO (Size.ofBytes 2)) true noClocks noBackend enabled extras
    simpa only [config, CanonicalCopy.Context.access, allocRange, treeDone, treeEq, ↓reduceIte] using fact
  have synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}} := by
    funext memory view
    exact MemoryCopyBridge.source_globals_synchronize context.prepared context.image context.extras context.globals memory view
  have unsized : place.layout.layout.backendRepr.isUnsized = false := by rw [layout]; decide +kernel
  have placeSize : place.layout.layout.size = Size.ofBytes 2 := by rw [layout]; exact PriorCellMetadata.u16_geometry.2.2.1
  have placeAccess := PhysicalMemoryWrite.get_place_write_of_access config context.pointers rfl state.machine
    ⟨place.mplace,localMemoryLayout place.layout⟩ id (tag 1) base 2 entry tree width (by decide) (by decide) cached present
    (by rw [allocation]; rfl) (by rw [allocation]; rfl) synchronize rfl access unsized placeSize pointer aligned runtimeSize
  have entryEq : {entry with allocation := entry.allocation.setExtra tree} = afterEntry := by
    rw [allocation]
    rfl
  have placeAccess' : getPlaceAllocMut state.machine.memory ⟨state.machine,none⟩
      ⟨place.mplace,localMemoryLayout place.layout⟩ config.runtime false config.globalKind config.globalHooks
      (PlaceMachine.accessHooks config) config.dynamicLayout =
      ⟨current,⟨state.machine,none⟩,some ⟨id,allocRange Size.ZERO afterEntry.allocation.byteSize,afterEntry.allocation⟩,
        .ok (some ⟨id,allocRange Size.ZERO afterEntry.allocation.byteSize,afterEntry.allocation⟩)⟩ := by
    have afterSize : afterEntry.allocation.byteSize = Size.ofBytes 2 := rfl
    rw [afterSize]
    simpa only [← entryEq, current] using placeAccess
  have currentPresent : current.live.find? (fun row => row.1 == id) = some (id,afterEntry) := by
    rw [← entryEq]
    exact MemoryCopyBridge.live_lookup_replaced state.machine.memory id _
  have mutation : Allocation.writeScalar config.runtime.base (allocRange Size.ZERO afterEntry.allocation.byteSize) word afterEntry.allocation =
      .ok () afterEntry.allocation := write_scalar_same config.runtime.base little runtimeWidth tree
  have abi : immediate_abi (.scalar word) (localMemoryLayout place.layout) config.runtime = .ok () := by
    rw [layout]
    exact word_abi _
  have operand := PhysicalMemoryWrite.scalar_write_of_allocation state.machine.memory current
    (PlaceMachine.AccessState.mk state.machine none) (PlaceMachine.AccessState.mk state.machine none)
    ⟨place.mplace,localMemoryLayout place.layout⟩ config.runtime false config.globalKind config.globalHooks
    (PlaceMachine.accessHooks config) config.dynamicLayout willValidate id afterEntry afterEntry.allocation word unsized abi placeAccess'
    currentPresent rfl mutation
  have memoryEq :
      {current with live := (current.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push (id,{afterEntry with allocation := afterEntry.allocation})} =
      {state.machine.memory with live := ((state.machine.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
        (id,{entry with allocation := sourceFor tree}))} := by
    exact MemoryCopyBridge.live_update_twice state.machine.memory id _ _
  rw [memoryEq] at operand
  change PlaceMachine.writeMemory config willValidate (.scalar word) place state = _
  unfold PlaceMachine.writeMemory
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
  have ghostMode : config.ghostMode = false := rfl
  rw [ghostMode,operand]
  unfold_internal ".PlaceMachine.commit"
  unfold_internal ".PlaceMachine.finish"
  have retain : config.retainTouched = fun machine _ => machine := rfl
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, retain,
    bind, EStateM.bind, pure, EStateM.pure]
  rfl

end DuplicatePrefix.S05ZeroCellCorrelatedWrite

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellCorrelatedWrite." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved correlated write dependency {dependency}"
