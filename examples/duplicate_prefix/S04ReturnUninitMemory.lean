import duplicate_prefix.PhysicalMemoryWrite
namespace DuplicatePrefix.S04ReturnUninitMemory
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem uninit_write_of_allocation {Prov Extra K S PX : Type} [DecidableEq K] [DecidableEq Prov] [PointerProvenance Prov]
    (memory current : MemoryState Prov Extra K) (hooks afterHooks : S)
    (place : MemoryOperandPlace Prov) (runtime : RuntimeTargetDataLayout)
    (ghost : Bool) (globalKind : Option K)
    (globals : GlobalAllocationHooks Prov Extra K S)
    (accessHooks : AllocationAccessHooks Prov Extra K S PX)
    (dynamic : DynamicLayoutResolver Prov Extra K S) (validate : MemoryOperandLayout → Bool)
    (offset count : UInt64)
    (id : AllocId) (entry : LocalAllocation Prov Extra K) (updated : Allocation Prov Extra)
    (sized : place.layout.backendRepr.isUnsized = false)
    (access : getPlaceAllocMut memory hooks place runtime ghost globalKind globals accessHooks dynamic =
      ⟨current,afterHooks,some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation⟩,
        .ok (some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation⟩)⟩)
    (present : current.live.find? (fun row => row.1 == id) = some (id,entry))
    (mutation : Allocation.writeUninit (allocRange (Size.ofBytes offset) (Size.ofBytes count)) runtime.pointerSize entry.allocation =
      .ok () updated) :
    writeImmediateToMplaceNoValidate memory hooks .uninit place runtime ghost globalKind globals accessHooks dynamic validate =
      ⟨{current with live := (current.live.filter fun row => row.1 != id).push (id,{entry with allocation := updated})},
        afterHooks,some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),updated⟩,.ok ()⟩ := by
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

end DuplicatePrefix.S04ReturnUninitMemory
