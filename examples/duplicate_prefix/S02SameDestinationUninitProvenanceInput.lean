import duplicate_prefix.ProvenanceCopy

namespace DuplicatePrefix.S02SameDestinationUninitProvenanceInput
open Miri.ABI Miri.Memory
set_option autoImplicit false

/-- The checks needed by copy preparation after clearing a return byte.
Fragment sorting is unnecessary: old fragments are copied individually. -/
structure DirectInput {Prov : Type} (self : ProvenanceMap Prov) (capacity : Nat) : Prop where
  pointerOrder : self.ptrs.toList.Pairwise (fun l r => l.1.bytes.toNat + 8 ≤ r.1.bytes.toNat)
  pointerBounds : ∀ entry ∈ self.ptrs, entry.1.bytes.toNat + 8 ≤ capacity
  fragmentsAvoidPointers : ProvenanceCopy.FragmentsAvoidPointers self
  fragmentCount : (self.byteFragments.getD #[]).size ≤ capacity + 16

end DuplicatePrefix.S02SameDestinationUninitProvenanceInput
