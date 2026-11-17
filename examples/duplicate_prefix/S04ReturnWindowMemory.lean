import duplicate_prefix.S04ReturnWindowPointer
import duplicate_prefix.PhysicalMemoryWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.S04ReturnWindowMemory
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
theorem get_place_write_of_access {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (canonical : config.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (place : MemoryOperandPlace Provenance)
    (id : AllocId) (tag : BorTag) (base offset count capacity : UInt64)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes capacity)
    (bounds : offset.toNat + count.toNat ≤ capacity.toNat)
    (mutable : entry.allocation.mutability = .Mut)
    (synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (before : config.beforeAllocationAccess = fun _ => pure ())
    (access : PlaceMachine.memoryAccess config true ⟨machine,none⟩ entry.allocation.extra id (.concrete tag)
      (allocRange (Size.ofBytes offset) (Size.ofBytes count)) = ⟨⟨machine,none⟩,tree,.ok ()⟩)
    (unsized : place.layout.backendRepr.isUnsized = false)
    (placeSize : place.layout.size = Size.ofBytes count)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id tag)) (Size.ofBytes (base+offset)))
    (aligned : place.mplace.misaligned = none)
    (runtimeSize : config.runtime.pointerSize = Size.ofBytes 8) :
    getPlaceAllocMut machine.memory ⟨machine,none⟩ place config.runtime false config.globalKind
      config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout =
      ⟨RetagEntry.updatedMemory machine.memory id entry tree,⟨machine,none⟩,
        some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation.setExtra tree⟩,
        .ok (some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation.setExtra tree⟩)⟩ := by
  have ptr := S04ReturnWindowPointer.get_ptr_write_of_access config pointers canonical machine id tag base offset count capacity entry tree
    width positive signedFits cached present size bounds mutable synchronize before access
  unfold getPlaceAllocMut
  unfold_internal ".Miri.Interpreter.selectedSizeAndAlign"
  simp only [unsized, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad, Id.run]
  rw [PhysicalMemoryWrite.pointer_arithmetic_eq]
  simp only [runtimeSize, placeSize, pointer, Bind.bind, Pure.pure, Id.instMonad, Id.run]
  erw [ptr]
  unfold_internal ".Miri.Interpreter.finishPlaceAccess"
  simp only [aligned]

theorem subrange_window (offset count : UInt64) (fits : offset.toNat + count.toNat < 2^64) :
    (allocRange (Size.ofBytes offset) (Size.ofBytes count)).subrange
      (allocRange Size.ZERO (Size.ofBytes count)) =
      .ok (allocRange (Size.ofBytes offset) (Size.ofBytes count)) := by
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes offset) count (by simpa [Size.ofBytes] using fits)
  simp [AllocRange.subrange, allocRange, Size.add, Size.ZERO, Size.ofBytes,
    Except.mapError, bind, Except.bind, pure, Except.pure] at endpoint ⊢
  simp [endpoint]

theorem scalar_write_of_allocation {Prov Extra K S PX : Type} [DecidableEq K] [DecidableEq Prov] [PointerProvenance Prov]
    (memory current : MemoryState Prov Extra K) (hooks afterHooks : S)
    (place : MemoryOperandPlace Prov) (runtime : RuntimeTargetDataLayout)
    (ghost : Bool) (globalKind : Option K)
    (globals : GlobalAllocationHooks Prov Extra K S)
    (accessHooks : AllocationAccessHooks Prov Extra K S PX)
    (dynamic : DynamicLayoutResolver Prov Extra K S) (validate : MemoryOperandLayout → Bool)
    (offset count : UInt64) (fits : offset.toNat + count.toNat < 2^64)
    (id : AllocId) (entry : LocalAllocation Prov Extra K) (updated : Allocation Prov Extra)
    (value : Scalar Prov)
    (sized : place.layout.backendRepr.isUnsized = false)
    (abi : immediate_abi (.scalar value) place.layout runtime = .ok ())
    (access : getPlaceAllocMut memory hooks place runtime ghost globalKind globals accessHooks dynamic =
      ⟨current,afterHooks,some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation⟩,
        .ok (some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation⟩)⟩)
    (present : current.live.find? (fun row => row.1 == id) = some (id,entry))
    (valueSize : value.size = Size.ofBytes count)
    (mutation : Allocation.writeScalar runtime.base (allocRange (Size.ofBytes offset) (Size.ofBytes count)) value entry.allocation =
      .ok () updated) :
    writeImmediateToMplaceNoValidate memory hooks (.scalar value) place runtime ghost globalKind globals accessHooks dynamic validate =
      ⟨{current with live := (current.live.filter fun row => row.1 != id).push (id,{entry with allocation := updated})},
        afterHooks,some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),updated⟩,.ok ()⟩ := by
  have stored := MemoryCopyBridge.set_live_exact current id entry updated present
  unfold writeImmediateToMplaceNoValidate
  simp only [sized, abi, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad]
  rw [access]
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  unfold_internal ".Miri.Interpreter.writeScalarAt"
  unfold_internal ".Miri.Interpreter.writeRange"
  simp only [valueSize, subrange_window offset count fits, Except.mapError, Bind.bind, Pure.pure, Except.bind, Except.pure, Id.instMonad]
  erw [mutation]
  unfold_internal ".Miri.Interpreter.commitAllocationMutation"
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  erw [stored]
  rfl

end DuplicatePrefix.S04ReturnWindowMemory
