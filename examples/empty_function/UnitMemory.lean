import Miri.Interpreter.MemoryOperand

namespace EmptyFunction.UnitMemory
open Miri Miri.ABI Miri.Memory Miri.Interpreter
set_option autoImplicit false

/-- A zero-byte mutable access does not resolve a pointer, touch allocations,
or run memory hooks. This holds for arbitrary memory, pointers and policies. -/
theorem zero_mutable_access {P E K H X : Type} [DecidableEq K]
    (memory : MemoryState P E K) (hooks : H) (target : PointerArithmetic)
    (pointer : Pointer (Option P)) (ghost : Bool) (kind : Option K)
    (globals : GlobalAllocationHooks P E K H)
    (access : AllocationAccessHooks P E K H X) :
    AllocationAccess.getPtrAllocMut memory hooks target pointer Size.ZERO ghost kind globals access =
      ⟨memory, hooks, none, .ok none⟩ := by
  cases ghost <;> with_unfolding_all rfl


end EmptyFunction.UnitMemory
