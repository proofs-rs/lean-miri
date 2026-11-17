import duplicate_prefix.S02SameDestinationUninitProvenanceClear

namespace DuplicatePrefix.S02SameDestinationUninitProvenanceResult
open Miri.ABI Miri.Memory
open ProvenanceCopy S02SameDestinationUninitProvenanceFragments S02SameDestinationUninitProvenanceClear
open S02SameDestinationUninitProvenanceInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
variable {Prov : Type}

/-- The actual clear supplies precisely the provenance facts checked by the
later copy. No sorting fact about byte fragments is required. -/
theorem after_clear (state updated : ProvenanceMap Prov) (range : AllocRange)
    (finish : Size) (data : Array UInt8)
    (valid : WellFormed state data.size)
    (nonzero : range.size.bytes ≠ 0)
    (endpoint : range.endExclusive = .ok finish)
    (storageFits : data.size < 18446744073709551616)
    (cleared : ProvenanceMap.clear range data (Size.ofBytes 8) state = .ok () updated) :
    DirectInput updated data.size := by
  obtain ⟨pointers,origins,count⟩ := clear_effect state updated range finish data nonzero endpoint
    (WellFormed.pointerBounds valid) storageFits cleared
  have subset : ∀ pointer ∈ updated.ptrs, pointer ∈ state.ptrs := by
    intro pointer member
    rw [pointers] at member
    exact (Array.mem_filter.mp member).1
  refine ⟨?_,?_,?_,?_⟩
  · rw [pointers]
    simpa only [Remaining,Array.toList_filter] using (WellFormed.pointerOrder valid).filter
      (fun entry => !(UInt64.ofNat (range.start.bytes.toNat-7) ≤ entry.1.bytes && entry.1.bytes < finish.bytes))
  · intro pointer member
    exact (WellFormed.pointerBounds valid) pointer (subset pointer member)
  · intro fragment member pointer atPointer
    rcases origins fragment member with old | ⟨origin,originMember,lower,upper⟩
    · exact (WellFormed.fragmentsAvoidPointers valid) fragment old pointer (subset pointer atPointer)
    · have originOriginal := mem_overlappingPointers state range finish origin originMember
      have separated := pairwise_intervals_disjoint state.ptrs.toList (WellFormed.pointerOrder valid) origin pointer
        (by simpa using originOriginal) (by simpa using subset pointer atPointer)
      rcases separated with equal | before | after
      · subst origin
        rw [pointers] at atPointer
        have outside := (Array.mem_filter.mp atPointer).2
        have inside := (Array.mem_filter.mp originMember).2
        have impossible : (!(UInt64.ofNat (range.start.bytes.toNat-7) ≤ pointer.1.bytes && pointer.1.bytes < finish.bytes)) = true := outside
        change (UInt64.ofNat (range.start.bytes.toNat-7) ≤ pointer.1.bytes && pointer.1.bytes < finish.bytes) = true at inside
        rw [inside] at impossible
        cases impossible
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
  · have oldCount := WellFormed.fragment_count valid
    omega

end DuplicatePrefix.S02SameDestinationUninitProvenanceResult
