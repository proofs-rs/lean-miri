import Miri.DataStructures.DedupRangeMap

/-! Kernel-checked behavior of the exact empty-range path in the real mutable
range iterator. -/
namespace DuplicatePrefix.RangeMapProof

open Miri.ABI Miri.DataStructures

variable {α : Type} [DecidableEq α]

theorem iter_mut_empty_exact (map : DedupRangeMap α) (offset : Size) :
    map.iterMut offset Size.ZERO = ⟨map, #[], #[], .ok ()⟩ := by
  simp [DedupRangeMap.iterMut, DedupRangeMap.iterMutWithClone, Size.ZERO]

#print axioms iter_mut_empty_exact

end DuplicatePrefix.RangeMapProof
