import duplicate_prefix.GlobalRelocationWordConversion
namespace DuplicatePrefix.GlobalRelocationSplice
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def patch (raw encoded : Array UInt8) (position : Nat) : Array UInt8 :=
  raw.extract 0 position ++ encoded ++ raw.extract (position+8) raw.size

theorem size (raw encoded : Array UInt8) (position : Nat)
    (bounds : position+8≤raw.size) (width : encoded.size=8) :
    (patch raw encoded position).size=raw.size := by
  simp only [patch,Array.size_append,Array.size_extract,Nat.min_self,Nat.sub_zero]
  rw [Nat.min_eq_left (by omega : position≤raw.size),width]
  omega

/-- A completed first relocation does not alter a later disjoint source window. -/
theorem later_window (raw encoded : Array UInt8) (first second : Nat)
    (separate : first+8≤second) (bounds : second+8≤raw.size) (width : encoded.size=8) :
    (patch raw encoded first).extract second (second+8) = raw.extract second (second+8) := by
  have patchSize := size raw encoded first (by omega) width
  have prefixSize : (raw.extract 0 first).size=first := by
    simp only [Array.size_extract,Nat.sub_zero,Nat.min_eq_left (by omega : first≤raw.size)]
  apply Array.ext
  · simp only [Array.size_extract,patchSize]
  · intro i validLeft validRight
    have upper : i<8 := by
      simpa only [Array.size_extract,Nat.min_eq_left bounds,Nat.add_sub_cancel_left] using validRight
    simp only [Array.getElem_extract]
    simp only [patch,Array.getElem_append]
    simp only [Array.size_append,prefixSize,width]
    split
    · omega
    · simp only [Array.getElem_extract]
      congr 1
      omega
end DuplicatePrefix.GlobalRelocationSplice
