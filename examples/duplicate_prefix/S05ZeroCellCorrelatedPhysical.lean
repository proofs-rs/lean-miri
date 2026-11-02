import duplicate_prefix.S05ZeroCellCorrelatedPrefix
import duplicate_prefix.OrdinaryPhysicalValidity

/-! Physical value/storage facts for the finite prefix.  These do not replace
reference validation or an adequacy argument for an ordinary caller domain. -/
namespace DuplicatePrefix.S05ZeroCellCorrelatedPhysical
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows
open S05ZeroCellCorrelatedPrefix OrdinaryPhysicalValidity
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

def sourceId : AllocId := ⟨1,by decide⟩
def destinationId : AllocId := ⟨2,by decide⟩
def source : Allocation Provenance BorrowTree :=
  ((Allocation.fromBytes (Prov := Provenance) #[11,22] Align.ONE .Mut).toOption.get (by decide)).withExtra w.tree
def destination : Allocation Provenance BorrowTree :=
  ((Allocation.fromBytes (Prov := Provenance) #[0] Align.ONE .Mut).toOption.get (by decide)).withExtra
    (BorrowTree.new (tag 7) (Size.ofBytes 1))

theorem distinct_allocations : sourceId ≠ destinationId := by decide

theorem source_physical : MutU8Slice source 0 2 := by
  constructor
  · constructor
    · rfl
    · rfl
    · cbv
    · change ProvenanceCopy.WellFormed (ProvenanceMap.new : ProvenanceMap Provenance) 2
      constructor <;> simp [ProvenanceMap.new, ProvenanceCopy.FragmentsAvoidPointers]
  · decide
  · decide
  · decide
  · rfl
  · intro index lower upper
    rfl

theorem destination_physical : BoolDestination destination 0 := by
  constructor
  · constructor
    · rfl
    · rfl
    · cbv
    · change ProvenanceCopy.WellFormed (ProvenanceMap.new : ProvenanceMap Provenance) 1
      constructor <;> simp [ProvenanceMap.new, ProvenanceCopy.FragmentsAvoidPointers]
  · decide
  · rfl

end DuplicatePrefix.S05ZeroCellCorrelatedPhysical

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05ZeroCellCorrelatedPhysical." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved correlated physical-prefix dependency {dependency}"
