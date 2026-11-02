import duplicate_prefix.S04ReturnProvenanceClear

namespace DuplicatePrefix.S03UninitProvenance
open Miri.ABI Miri.Memory
set_option autoImplicit false

/-- The actual clear operation preserves the whole-pointer storage bounds
needed by later physical stores. Boundary-crossing pointers may become byte
fragments; no fragment ordering or complete post-clear WellFormed claim is
needed or asserted here. The original caller may still supply full WellFormed.
This is a local consequence of an exact operation equation, not a new caller
premise or an assumption that the configured call succeeds. -/
theorem clear_pointer_bounds {Prov : Type} (state updated : ProvenanceMap Prov)
    (range : AllocRange) (finish : Size) (data : Array UInt8) (capacity : Nat)
    (endpoint : range.endExclusive = .ok finish)
    (bounds : ∀ entry ∈ state.ptrs, entry.1.bytes.toNat + 8 ≤ capacity)
    (cleared : ProvenanceMap.clear range data (Size.ofBytes 8) state = .ok () updated) :
    ∀ entry ∈ updated.ptrs, entry.1.bytes.toNat + 8 ≤ capacity := by
  intro entry member
  exact bounds entry (S04ReturnProvenanceClear.clear_pointer_subset state updated range finish data endpoint cleared entry member)

end DuplicatePrefix.S03UninitProvenance
