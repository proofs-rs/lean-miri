import duplicate_prefix.S04ReturnResolvedWindowPointer
import duplicate_prefix.PhysicalMemoryWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.S04ReturnResolvedWindowMemory
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
theorem get_place_write_of_access {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (canonical : config.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (place : MemoryOperandPlace Provenance)
    (id : AllocId) (provenance : Provenance) (extra : ProvenanceExtra) (base offset count capacity : UInt64)
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
    (access : PlaceMachine.memoryAccess config true ⟨machine,none⟩ entry.allocation.extra id extra
      (allocRange (Size.ofBytes offset) (Size.ofBytes count)) = ⟨⟨machine,none⟩,tree,.ok ()⟩)
    (unsized : place.layout.backendRepr.isUnsized = false)
    (placeSize : place.layout.size = Size.ofBytes count)
    (pointer : place.mplace.ptr = Pointer.new (some provenance) (Size.ofBytes (base+offset)))
    (aligned : place.mplace.misaligned = none)
    (runtimeSize : config.runtime.pointerSize = Size.ofBytes 8)
    (resolved : config.resolvePointer machine.memory
      (Pointer.new (some provenance) (Size.ofBytes (base + offset))) (Int.ofNat count.toNat) machine =
      .ok (.ok ⟨id,Size.ofBytes offset,extra⟩) machine) :
    getPlaceAllocMut machine.memory ⟨machine,none⟩ place config.runtime false config.globalKind
      config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout =
      ⟨RetagEntry.updatedMemory machine.memory id entry tree,⟨machine,none⟩,
        some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation.setExtra tree⟩,
        .ok (some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation.setExtra tree⟩)⟩ := by
  have ptr := S04ReturnResolvedWindowPointer.get_ptr_write_of_access config pointers canonical machine id provenance extra base offset count capacity entry tree
    width positive signedFits cached present size bounds mutable synchronize before access resolved
  unfold getPlaceAllocMut
  unfold_internal ".Miri.Interpreter.selectedSizeAndAlign"
  simp only [unsized, Bool.false_eq_true, ↓reduceIte, Bind.bind, Pure.pure, Id.instMonad, Id.run]
  rw [PhysicalMemoryWrite.pointer_arithmetic_eq]
  simp only [runtimeSize, placeSize, pointer, Bind.bind, Pure.pure, Id.instMonad, Id.run]
  erw [ptr]
  unfold_internal ".Miri.Interpreter.finishPlaceAccess"
  simp only [aligned]

end DuplicatePrefix.S04ReturnResolvedWindowMemory
