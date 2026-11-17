import duplicate_prefix.PhysicalPointerAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PhysicalMemoryWrite
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Lean Elab
private def sourceName (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected unique memory scalar helper {suffix}"
elab "immediate_abi" : term => return mkConst (← sourceName ".Miri.Interpreter.immediateMatchesAbi")

elab "operand_arithmetic" : term => return mkConst (← sourceName ".Miri.Interpreter.pointerArithmeticFor")

theorem pointer_arithmetic_eq (runtime : RuntimeTargetDataLayout) :
    operand_arithmetic runtime = .ok ⟨runtime.pointerSize⟩ := by
  unfold_internal ".Miri.Interpreter.pointerArithmeticFor"
  simp [RuntimeTargetDataLayout.pointerSizeIn, RuntimeTargetDataLayout.pointerSpecIn,
    RuntimeTargetDataLayout.pointerSize, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem get_place_write_of_access {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (canonical : config.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (place : MemoryOperandPlace Provenance)
    (id : AllocId) (tag : BorTag) (base count : UInt64)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes count)
    (mutable : entry.allocation.mutability = .Mut)
    (synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (before : config.beforeAllocationAccess = fun _ => pure ())
    (access : PlaceMachine.memoryAccess config true ⟨machine,none⟩ entry.allocation.extra id (.concrete tag)
      (allocRange Size.ZERO (Size.ofBytes count)) = ⟨⟨machine,none⟩,tree,.ok ()⟩)
    (unsized : place.layout.backendRepr.isUnsized = false)
    (placeSize : place.layout.size = Size.ofBytes count)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id tag)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (runtimeSize : config.runtime.pointerSize = Size.ofBytes 8) :
    getPlaceAllocMut machine.memory ⟨machine,none⟩ place config.runtime false config.globalKind
      config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout =
      ⟨RetagEntry.updatedMemory machine.memory id entry tree,⟨machine,none⟩,
        some ⟨id,allocRange Size.ZERO (Size.ofBytes count),entry.allocation.setExtra tree⟩,
        .ok (some ⟨id,allocRange Size.ZERO (Size.ofBytes count),entry.allocation.setExtra tree⟩)⟩ := by
  have ptr := PhysicalPointerAccess.get_ptr_write_of_access config pointers canonical machine id tag base count entry tree
    width positive signedFits cached present size mutable synchronize before access
  unfold getPlaceAllocMut
  unfold_internal ".Miri.Interpreter.selectedSizeAndAlign"
  simp only [unsized, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad, Id.run]
  rw [pointer_arithmetic_eq]
  simp only [runtimeSize, placeSize, pointer, Bind.bind, Pure.pure, Id.instMonad, Id.run]
  erw [ptr]
  unfold_internal ".Miri.Interpreter.finishPlaceAccess"
  simp only [aligned]

#print axioms get_place_write_of_access

theorem get_place_ghost {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (canonical : config.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (place : MemoryOperandPlace Provenance)
    (id : AllocId) (tag : BorTag) (base count : UInt64)
    (entry : LocalAllocation Provenance BorrowTree K) (write : Bool)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes count)
    (mutable : entry.allocation.mutability = .Mut)
    (synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (unsized : place.layout.backendRepr.isUnsized = false)
    (placeSize : place.layout.size = Size.ofBytes count)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id tag)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (runtimeSize : config.runtime.pointerSize = Size.ofBytes 8) :
    (if write then getPlaceAllocMut machine.memory ⟨machine,none⟩ place config.runtime true config.globalKind
        config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout
      else getPlaceAlloc machine.memory ⟨machine,none⟩ place config.runtime true config.globalKind
        config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout) =
      ⟨machine.memory,⟨machine,none⟩,some ⟨id,allocRange Size.ZERO (Size.ofBytes count),entry.allocation⟩,
        .ok (some ⟨id,allocRange Size.ZERO (Size.ofBytes count),entry.allocation⟩)⟩ := by
  have ptr := PhysicalPointerAccess.get_ptr_ghost config pointers canonical machine id tag base count entry write
    width positive signedFits cached present size mutable synchronize
  cases write
  · change getPlaceAlloc machine.memory ⟨machine,none⟩ place config.runtime true config.globalKind
      config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = _
    change AllocationAccess.getPtrAlloc machine.memory ⟨machine,none⟩ ⟨Size.ofBytes 8⟩
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes base)) (Size.ofBytes count) true
      config.globalKind config.globalHooks (PlaceMachine.accessHooks config) = _ at ptr
    unfold getPlaceAlloc
    unfold_internal ".Miri.Interpreter.selectedSizeAndAlign"
    simp only [unsized, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad, Id.run]
    rw [pointer_arithmetic_eq]
    simp only [runtimeSize, placeSize, pointer, Bind.bind, Pure.pure, Id.instMonad, Id.run]
    erw [ptr]
    unfold_internal ".Miri.Interpreter.finishPlaceAccess"
    simp only [aligned]
  · change getPlaceAllocMut machine.memory ⟨machine,none⟩ place config.runtime true config.globalKind
      config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = _
    change AllocationAccess.getPtrAllocMut machine.memory ⟨machine,none⟩ ⟨Size.ofBytes 8⟩
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes base)) (Size.ofBytes count) true
      config.globalKind config.globalHooks (PlaceMachine.accessHooks config) = _ at ptr
    unfold getPlaceAllocMut
    unfold_internal ".Miri.Interpreter.selectedSizeAndAlign"
    simp only [unsized, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad, Id.run]
    rw [pointer_arithmetic_eq]
    simp only [runtimeSize, placeSize, pointer, Bind.bind, Pure.pure, Id.instMonad, Id.run]
    erw [ptr]
    unfold_internal ".Miri.Interpreter.finishPlaceAccess"
    simp only [aligned]

#print axioms get_place_ghost

theorem subrange_full (size : Size) :
    (allocRange Size.ZERO size).subrange (allocRange Size.ZERO size) = .ok (allocRange Size.ZERO size) := by
  cases size
  simp [AllocRange.subrange, allocRange, AllocRange.endExclusive, AllocRange.end, Size.add,
    Size.ZERO, Size.ofBytes, Except.mapError, bind, Except.bind, pure, Except.pure]

theorem scalar_write_of_allocation {Prov Extra K S PX : Type} [DecidableEq K] [DecidableEq Prov] [PointerProvenance Prov]
    (memory current : MemoryState Prov Extra K) (hooks afterHooks : S)
    (place : MemoryOperandPlace Prov) (runtime : RuntimeTargetDataLayout)
    (ghost : Bool) (globalKind : Option K)
    (globals : GlobalAllocationHooks Prov Extra K S)
    (accessHooks : AllocationAccessHooks Prov Extra K S PX)
    (dynamic : DynamicLayoutResolver Prov Extra K S) (validate : MemoryOperandLayout → Bool)
    (id : AllocId) (entry : LocalAllocation Prov Extra K) (updated : Allocation Prov Extra)
    (value : Scalar Prov)
    (sized : place.layout.backendRepr.isUnsized = false)
    (abi : immediate_abi (.scalar value) place.layout runtime = .ok ())
    (access : getPlaceAllocMut memory hooks place runtime ghost globalKind globals accessHooks dynamic =
      ⟨current,afterHooks,some ⟨id,allocRange Size.ZERO entry.allocation.byteSize,entry.allocation⟩,
        .ok (some ⟨id,allocRange Size.ZERO entry.allocation.byteSize,entry.allocation⟩)⟩)
    (present : current.live.find? (fun row => row.1 == id) = some (id,entry))
    (valueSize : value.size = entry.allocation.byteSize)
    (mutation : Allocation.writeScalar runtime.base (allocRange Size.ZERO entry.allocation.byteSize) value entry.allocation =
      .ok () updated) :
    writeImmediateToMplaceNoValidate memory hooks (.scalar value) place runtime ghost globalKind globals accessHooks dynamic validate =
      ⟨{current with live := (current.live.filter fun row => row.1 != id).push (id,{entry with allocation := updated})},
        afterHooks,some ⟨id,allocRange Size.ZERO entry.allocation.byteSize,updated⟩,.ok ()⟩ := by
  have stored := MemoryCopyBridge.set_live_exact current id entry updated present
  unfold writeImmediateToMplaceNoValidate
  simp only [sized, abi, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad]
  rw [access]
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  unfold_internal ".Miri.Interpreter.writeScalarAt"
  unfold_internal ".Miri.Interpreter.writeRange"
  simp only [valueSize, subrange_full, Except.mapError, Bind.bind, Pure.pure, Except.bind, Except.pure, Id.instMonad]
  erw [mutation]
  unfold_internal ".Miri.Interpreter.commitAllocationMutation"
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  erw [stored]
  rfl

theorem uninit_write_of_allocation {Prov Extra K S PX : Type} [DecidableEq K] [DecidableEq Prov] [PointerProvenance Prov]
    (memory current : MemoryState Prov Extra K) (hooks afterHooks : S)
    (place : MemoryOperandPlace Prov) (runtime : RuntimeTargetDataLayout)
    (ghost : Bool) (globalKind : Option K)
    (globals : GlobalAllocationHooks Prov Extra K S)
    (accessHooks : AllocationAccessHooks Prov Extra K S PX)
    (dynamic : DynamicLayoutResolver Prov Extra K S) (validate : MemoryOperandLayout → Bool)
    (id : AllocId) (entry : LocalAllocation Prov Extra K) (updated : Allocation Prov Extra)
    (sized : place.layout.backendRepr.isUnsized = false)
    (access : getPlaceAllocMut memory hooks place runtime ghost globalKind globals accessHooks dynamic =
      ⟨current,afterHooks,some ⟨id,allocRange Size.ZERO entry.allocation.byteSize,entry.allocation⟩,
        .ok (some ⟨id,allocRange Size.ZERO entry.allocation.byteSize,entry.allocation⟩)⟩)
    (present : current.live.find? (fun row => row.1 == id) = some (id,entry))
    (mutation : Allocation.writeUninit (allocRange Size.ZERO entry.allocation.byteSize) runtime.pointerSize entry.allocation =
      .ok () updated) :
    writeImmediateToMplaceNoValidate memory hooks .uninit place runtime ghost globalKind globals accessHooks dynamic validate =
      ⟨{current with live := (current.live.filter fun row => row.1 != id).push (id,{entry with allocation := updated})},
        afterHooks,some ⟨id,allocRange Size.ZERO entry.allocation.byteSize,updated⟩,.ok ()⟩ := by
  have stored := MemoryCopyBridge.set_live_exact current id entry updated present
  have abi : immediate_abi (.uninit : Immediate Prov) place.layout runtime = .ok () := by
    unfold_internal ".Miri.Interpreter.immediateMatchesAbi"
    simp only [sized, Bool.false_eq_true, ↓reduceIte, pure, Except.pure]
  unfold writeImmediateToMplaceNoValidate
  simp only [sized, abi, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad]
  rw [access]
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  unfold_internal ".Miri.Interpreter.writeUninitFull"
  erw [mutation]
  unfold_internal ".Miri.Interpreter.commitAllocationMutation"
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  erw [stored]
  rfl

#print axioms uninit_write_of_allocation

#print axioms scalar_write_of_allocation
end DuplicatePrefix.PhysicalMemoryWrite
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.PhysicalMemoryWrite.scalar_write_of_allocation,
      ``DuplicatePrefix.PhysicalMemoryWrite.get_place_write_of_access,
      ``DuplicatePrefix.PhysicalMemoryWrite.pointer_arithmetic_eq,
      ``DuplicatePrefix.PhysicalMemoryWrite.uninit_write_of_allocation,
      ``DuplicatePrefix.PhysicalMemoryWrite.get_place_ghost] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved physical memory scalar dependency {dependency}"
