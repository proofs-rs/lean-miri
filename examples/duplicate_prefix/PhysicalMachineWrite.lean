import duplicate_prefix.PhysicalMemoryWrite
import duplicate_prefix.CanonicalConfigFacts
import duplicate_prefix.ReturnTreeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PhysicalMachineWrite
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
abbrev Context := CanonicalCopy.Context Unit Unit Unit Unit Unit Unit Unit Unit Machine.MinimalHost

abbrev slotTree (root child : BorTag) (count : UInt64) (written : Bool) :=
  BorrowRangeAccess.canonicalChildTree root child
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes count) (BorrowRangeAccess.childLocation written))

theorem bool_abi (runtime : RuntimeTargetDataLayout) (value : Bool) :
    immediate_abi (.scalar (Scalar.fromBool value : Scalar Provenance))
      (localMemoryLayout RootCompilerFacts.boolLayout) runtime = .ok () := by
  cases value <;> with_unfolding_all rfl

theorem usize_abi (runtime : RuntimeTargetDataLayout) (value : UInt64) :
    immediate_abi (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 value) : Scalar Provenance))
      (localMemoryLayout RootCompilerFacts.usizeLayout) runtime = .ok () := by
  with_unfolding_all rfl

abbrev parentWrittenTree (root child : BorTag) (count : UInt64) :=
  BorrowRangeAccess.canonicalChildTree root child
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes count) ReturnTreeAccess.parentWrittenLocation)

theorem uninit_on_context_of_tree (context : Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (id : AllocId) (tag : BorTag) (base count : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (tree : BorrowTree)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
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
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (treeDone : (entry.allocation.extra.performBorrowAccessRange (.concrete tag) Size.ZERO (Size.ofBytes count)
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (treeEq : (entry.allocation.extra.performBorrowAccessRange (.concrete tag) Size.ZERO (Size.ofBytes count)
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed).tree = tree)
    (unsized : place.layout.layout.backendRepr.isUnsized = false)
    (placeSize : place.layout.layout.size = Size.ofBytes count)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id tag)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8) :
    ∃ updated, PlaceMachine.writeMemory context.access (fun _ => false) .uninit place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
          (id,{entry with allocation := updated}))}}} ∧
      updated.extra = tree ∧ updated.byteSize = entry.allocation.byteSize ∧ updated.len = entry.allocation.len ∧
      updated.initializationMask = InitMask.new entry.allocation.byteSize false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot entry.allocation ∧
      updated.mutability = entry.allocation.mutability := by
  let config := context.access
  let afterEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {entry with allocation := entry.allocation.setExtra tree}
  let current := RetagEntry.updatedMemory state.machine.memory id entry tree
  have access : PlaceMachine.memoryAccess config true ⟨state.machine,none⟩ entry.allocation.extra id (.concrete tag)
      (allocRange Size.ZERO (Size.ofBytes count)) = ⟨⟨state.machine,none⟩,tree,.ok ()⟩ := by
    have fact := MemoryCopyBridge.source_memory_access_exact context.prepared context.image context.maximum context.fuel
      context.globalHooks context.pointers context.extras state.machine tracker entry.allocation.extra id (.concrete tag)
      (allocRange Size.ZERO (Size.ofBytes count)) true noClocks noBackend enabled extras
    simpa only [config, CanonicalCopy.Context.access, allocRange, treeDone, treeEq, ↓reduceIte] using fact
  have synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}} := by
    funext memory view
    exact MemoryCopyBridge.source_globals_synchronize context.prepared context.image context.extras context.globals memory view
  have placeAccess := PhysicalMemoryWrite.get_place_write_of_access config context.pointers rfl state.machine
    ⟨place.mplace,localMemoryLayout place.layout⟩ id tag base count entry tree width positive signedFits cached present size
    mutable synchronize rfl access unsized placeSize pointer aligned runtimeSize
  have currentPresent : current.live.find? (fun row => row.1 == id) = some (id,afterEntry) :=
    MemoryCopyBridge.live_lookup_replaced state.machine.memory id afterEntry
  have positiveNat : 0 < afterEntry.allocation.byteSize.bytes.toNat := by
    change 0 < entry.allocation.byteSize.bytes.toNat
    rw [size]
    simpa only [Size.ofBytes, UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] using positive
  obtain ⟨updated, mutation, extra, bytes, length, mask, prov, snapshot, mutability⟩ :=
    PhysicalScalarReturn.write_uninit_whole_exists afterEntry.allocation storage mutable maskLength provenance positiveNat
  have afterSize : afterEntry.allocation.byteSize = Size.ofBytes count := size
  have placeAccess' : getPlaceAllocMut state.machine.memory ⟨state.machine,none⟩
      ⟨place.mplace,localMemoryLayout place.layout⟩ config.runtime false config.globalKind config.globalHooks
      (PlaceMachine.accessHooks config) config.dynamicLayout =
      ⟨current,⟨state.machine,none⟩,some ⟨id,allocRange Size.ZERO afterEntry.allocation.byteSize,afterEntry.allocation⟩,
        .ok (some ⟨id,allocRange Size.ZERO afterEntry.allocation.byteSize,afterEntry.allocation⟩)⟩ := by
    simpa only [afterSize, current, afterEntry] using placeAccess
  have operand := PhysicalMemoryWrite.uninit_write_of_allocation state.machine.memory current
    (PlaceMachine.AccessState.mk state.machine none) (PlaceMachine.AccessState.mk state.machine none)
    ⟨place.mplace,localMemoryLayout place.layout⟩ config.runtime false config.globalKind config.globalHooks
    (PlaceMachine.accessHooks config) config.dynamicLayout (fun _ => false) id afterEntry updated unsized placeAccess'
    currentPresent (by rw [runtimeSize]; exact mutation)
  have memoryEq :
      {current with live := (current.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push (id,{afterEntry with allocation := updated})} =
      {state.machine.memory with live := ((state.machine.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
        (id,{entry with allocation := updated}))} :=
    MemoryCopyBridge.live_update_twice state.machine.memory id afterEntry {entry with allocation := updated}
  rw [memoryEq] at operand
  refine ⟨updated, ?_, extra, bytes, length, mask, prov, snapshot, mutability⟩
  change PlaceMachine.writeMemory config (fun _ => false) .uninit place state = _
  unfold PlaceMachine.writeMemory
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
  have ghostMode : config.ghostMode = false := rfl
  rw [ghostMode]
  rw [operand]
  unfold_internal ".PlaceMachine.commit"
  unfold_internal ".PlaceMachine.finish"
  have retain : config.retainTouched = fun machine _ => machine := rfl
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, retain,
    bind, EStateM.bind, pure, EStateM.pure]

theorem scalar_on_context_of_tree (context : Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (id : AllocId) (tag : BorTag) (base count : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (tree : BorrowTree) (value : Scalar Provenance) (bits : U128)
    (small : count = 1 ∨ count = 8)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes count)
    (mutable : entry.allocation.mutability = .Mut)
    (maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (valueSize : value.size = entry.allocation.byteSize)
    (converted : value.toBitsOrPtrInternal entry.allocation.byteSize = .ok (.bits bits))
    (abi : immediate_abi (.scalar value) (localMemoryLayout place.layout) context.access.runtime = .ok ())
    (runtimeWidth : context.access.runtime.base.pointerWidth = .w64)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (provenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (enabled : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (treeDone : (entry.allocation.extra.performBorrowAccessRange (.concrete tag) Size.ZERO (Size.ofBytes count)
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (treeEq : (entry.allocation.extra.performBorrowAccessRange (.concrete tag) Size.ZERO (Size.ofBytes count)
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed).tree = tree)
    (unsized : place.layout.layout.backendRepr.isUnsized = false)
    (placeSize : place.layout.layout.size = Size.ofBytes count)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id tag)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8)
    (willValidate : MemoryOperandLayout → Bool := fun _ => false) :
    ∃ updated, PlaceMachine.writeMemory context.access willValidate (.scalar value) place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
          (id,{entry with allocation := updated}))}}} ∧
      updated.extra = tree ∧ updated.byteSize = entry.allocation.byteSize ∧ updated.len = entry.allocation.len ∧
      updated.initializationMask = InitMask.new entry.allocation.byteSize true ∧
      updated.provenanceMap = ProvenanceMap.new ∧ target_bytes context.access.runtime.base entry.allocation.byteSize bits = .ok (AllocationCopy.snapshot updated) ∧
      updated.mutability = entry.allocation.mutability := by
  let config := context.access
  let afterEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {entry with allocation := entry.allocation.setExtra tree}
  let current := RetagEntry.updatedMemory state.machine.memory id entry tree
  have access : PlaceMachine.memoryAccess config true ⟨state.machine,none⟩ entry.allocation.extra id (.concrete tag)
      (allocRange Size.ZERO (Size.ofBytes count)) = ⟨⟨state.machine,none⟩,tree,.ok ()⟩ := by
    have fact := MemoryCopyBridge.source_memory_access_exact context.prepared context.image context.maximum context.fuel
      context.globalHooks context.pointers context.extras state.machine tracker entry.allocation.extra id (.concrete tag)
      (allocRange Size.ZERO (Size.ofBytes count)) true noClocks noBackend enabled extras
    simpa only [config, CanonicalCopy.Context.access, allocRange, treeDone, treeEq, ↓reduceIte] using fact
  have synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}} := by
    funext memory view
    exact MemoryCopyBridge.source_globals_synchronize context.prepared context.image context.extras context.globals memory view
  have placeAccess := PhysicalMemoryWrite.get_place_write_of_access config context.pointers rfl state.machine
    ⟨place.mplace,localMemoryLayout place.layout⟩ id tag base count entry tree width positive signedFits cached present size
    mutable synchronize rfl access unsized placeSize pointer aligned runtimeSize
  have currentPresent : current.live.find? (fun row => row.1 == id) = some (id,afterEntry) :=
    MemoryCopyBridge.live_lookup_replaced state.machine.memory id afterEntry
  have positiveNat : 0 < afterEntry.allocation.byteSize.bytes.toNat := by
    change 0 < entry.allocation.byteSize.bytes.toNat
    rw [size]
    simpa only [Size.ofBytes, UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] using positive
  have smallSize : afterEntry.allocation.byteSize = Size.ofBytes 1 ∨ afterEntry.allocation.byteSize = Size.ofBytes 8 := by
    change entry.allocation.byteSize = Size.ofBytes 1 ∨ entry.allocation.byteSize = Size.ofBytes 8
    rcases small with one | eight
    · exact Or.inl (size.trans (congrArg Size.ofBytes one))
    · exact Or.inr (size.trans (congrArg Size.ofBytes eight))
  obtain ⟨updated, mutation, extra, bytes, length, mask, prov, encoding, mutability⟩ :=
    PhysicalScalarReturn.write_small_integer_exists config.runtime.base afterEntry.allocation value bits
      storage mutable maskLength maskValid provenance runtimeWidth smallSize converted
  have afterSize : afterEntry.allocation.byteSize = Size.ofBytes count := size
  have placeAccess' : getPlaceAllocMut state.machine.memory ⟨state.machine,none⟩
      ⟨place.mplace,localMemoryLayout place.layout⟩ config.runtime false config.globalKind config.globalHooks
      (PlaceMachine.accessHooks config) config.dynamicLayout =
      ⟨current,⟨state.machine,none⟩,some ⟨id,allocRange Size.ZERO afterEntry.allocation.byteSize,afterEntry.allocation⟩,
        .ok (some ⟨id,allocRange Size.ZERO afterEntry.allocation.byteSize,afterEntry.allocation⟩)⟩ := by
    simpa only [afterSize, current, afterEntry] using placeAccess
  have operand := PhysicalMemoryWrite.scalar_write_of_allocation state.machine.memory current
    (PlaceMachine.AccessState.mk state.machine none) (PlaceMachine.AccessState.mk state.machine none)
    ⟨place.mplace,localMemoryLayout place.layout⟩ config.runtime false config.globalKind config.globalHooks
    (PlaceMachine.accessHooks config) config.dynamicLayout willValidate id afterEntry updated value unsized abi placeAccess'
    currentPresent valueSize mutation
  have memoryEq :
      {current with live := (current.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push (id,{afterEntry with allocation := updated})} =
      {state.machine.memory with live := ((state.machine.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
        (id,{entry with allocation := updated}))} :=
    MemoryCopyBridge.live_update_twice state.machine.memory id afterEntry {entry with allocation := updated}
  rw [memoryEq] at operand
  refine ⟨updated, ?_, extra, bytes, length, mask, prov, encoding, mutability⟩
  change PlaceMachine.writeMemory config willValidate (.scalar value) place state = _
  unfold PlaceMachine.writeMemory
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind]
  have ghostMode : config.ghostMode = false := rfl
  rw [ghostMode]
  rw [operand]
  unfold_internal ".PlaceMachine.commit"
  unfold_internal ".PlaceMachine.finish"
  have retain : config.retainTouched = fun machine _ => machine := rfl
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, retain,
    bind, EStateM.bind, pure, EStateM.pure]

theorem bool_parent_slot (context : Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (id : AllocId) (root child : BorTag) (written : Bool) (base count : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (value : Bool) (one : count = 1)
    (layout : place.layout = RootCompilerFacts.boolLayout)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes count)
    (mutable : entry.allocation.mutability = .Mut)
    (maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (runtimeWidth : context.access.runtime.base.pointerWidth = .w64)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (provenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (enabled : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (rootFree : tracker.global.protectedTags.contains root = false)
    (childFree : tracker.global.protectedTags.contains child = false)
    (initialTree : entry.allocation.extra = slotTree root child count written)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id root)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8)
    (willValidate : MemoryOperandLayout → Bool := fun _ => false) :
    ∃ updated, PlaceMachine.writeMemory context.access willValidate (.scalar (Scalar.fromBool value)) place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
          (id,{entry with allocation := updated}))}}} ∧
      updated.extra = parentWrittenTree root child count ∧ updated.byteSize = entry.allocation.byteSize ∧ updated.len = entry.allocation.len ∧
      updated.initializationMask = InitMask.new entry.allocation.byteSize true ∧
      updated.provenanceMap = ProvenanceMap.new ∧ target_bytes context.access.runtime.base entry.allocation.byteSize (if value then 1 else 0) = .ok (AllocationCopy.snapshot updated) ∧
      updated.mutability = entry.allocation.mutability := by
  have borrow := ReturnTreeAccess.parent_write_full root child count written tracker.global.protectedTags
    rootFree childFree positive
  have done : (entry.allocation.extra.performBorrowAccessRange (.concrete root) Size.ZERO (Size.ofBytes count)
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    rw [initialTree]
    exact borrow.1
  have changed : (entry.allocation.extra.performBorrowAccessRange (.concrete root) Size.ZERO (Size.ofBytes count)
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed).tree = parentWrittenTree root child count := by
    rw [initialTree]
    exact borrow.2
  have valueSize : (Scalar.fromBool value : Scalar Provenance).size = entry.allocation.byteSize := by
    rw [size,one]
    cases value <;> rfl
  have converted : (Scalar.fromBool value : Scalar Provenance).toBitsOrPtrInternal entry.allocation.byteSize =
      .ok (.bits (if value then 1 else 0)) := by
    rw [size,one]
    exact PhysicalScalarReturn.bool_bits value
  have abi : immediate_abi (.scalar (Scalar.fromBool value : Scalar Provenance))
      (localMemoryLayout place.layout) context.access.runtime = .ok () := by
    rw [layout]
    exact bool_abi context.access.runtime value
  have unsized : place.layout.layout.backendRepr.isUnsized = false := by rw [layout]; decide +kernel
  have placeSize : place.layout.layout.size = Size.ofBytes count := by rw [layout,one]; decide +kernel
  exact scalar_on_context_of_tree context state place id root base count entry tracker (parentWrittenTree root child count)
    (Scalar.fromBool value) (if value then 1 else 0) (Or.inl one) width positive signedFits cached present size
    mutable maskValid valueSize converted abi runtimeWidth storage maskLength provenance noClocks noBackend enabled extras
    done changed unsized placeSize pointer aligned runtimeSize willValidate

#print axioms bool_parent_slot

theorem uninit_protected_slot (context : Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (id : AllocId) (root child : BorTag) (written : Bool) (base count : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
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
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (rootFree : tracker.global.protectedTags.contains root = false)
    (childHeld : tracker.global.protectedTags.contains child = true)
    (distinct : root ≠ child)
    (initialTree : entry.allocation.extra = slotTree root child count written)
    (unsized : place.layout.layout.backendRepr.isUnsized = false)
    (placeSize : place.layout.layout.size = Size.ofBytes count)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id child)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8) :
    ∃ updated, PlaceMachine.writeMemory context.access (fun _ => false) .uninit place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
          (id,{entry with allocation := updated}))}}} ∧
      updated.extra = slotTree root child count true ∧ updated.byteSize = entry.allocation.byteSize ∧ updated.len = entry.allocation.len ∧
      updated.initializationMask = InitMask.new entry.allocation.byteSize false ∧
      updated.provenanceMap = ProvenanceMap.new ∧ AllocationCopy.snapshot updated = AllocationCopy.snapshot entry.allocation ∧
      updated.mutability = entry.allocation.mutability := by
  have borrow := ReturnTreeAccess.slot_child_write_full root child count written tracker.global.protectedTags
    rootFree childHeld distinct positive
  have done : (entry.allocation.extra.performBorrowAccessRange (.concrete child) Size.ZERO (Size.ofBytes count)
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    rw [initialTree]
    exact borrow.1
  have changed : (entry.allocation.extra.performBorrowAccessRange (.concrete child) Size.ZERO (Size.ofBytes count)
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed).tree = slotTree root child count true := by
    rw [initialTree]
    exact borrow.2
  exact uninit_on_context_of_tree context state place id child base count entry tracker (slotTree root child count true)
    width positive signedFits cached present size mutable storage maskLength provenance noClocks noBackend enabled extras
    done changed unsized placeSize pointer aligned runtimeSize

#print axioms uninit_protected_slot

#print axioms uninit_on_context_of_tree
end DuplicatePrefix.PhysicalMachineWrite
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.PhysicalMachineWrite.uninit_on_context_of_tree,
      ``DuplicatePrefix.PhysicalMachineWrite.uninit_protected_slot,
      ``DuplicatePrefix.PhysicalMachineWrite.scalar_on_context_of_tree,
      ``DuplicatePrefix.PhysicalMachineWrite.bool_abi, ``DuplicatePrefix.PhysicalMachineWrite.usize_abi,
      ``DuplicatePrefix.PhysicalMachineWrite.bool_parent_slot] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved physical machine write dependency {dependency}"
