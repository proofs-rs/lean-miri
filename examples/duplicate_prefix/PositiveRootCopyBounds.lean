import Lean.Elab.Command
import duplicate_prefix.Bounds
namespace DuplicatePrefix.PositiveRootCopyBounds
open Miri.ABI Miri.Memory
set_option maxHeartbeats 4000000

theorem guarded (len n offset capacity : UInt64)
    (within : n≤len/2) (slice : offset.toNat+len.toNat≤capacity.toNat) :
    n.toNat<2^63 ∧ n.toNat+n.toNat≤len.toNat ∧
      offset.toNat+n.toNat≤capacity.toNat ∧ offset.toNat+n.toNat+n.toNat≤capacity.toNat := by
  have notGt : ¬n>len/2 := by
    intro h
    have low := UInt64.le_iff_toNat_le.mp within
    have high := UInt64.lt_iff_toNat_lt.mp h
    omega
  have twice := usize_guard notGt
  have bounded : len.toNat<2^64 := UInt64.toNat_lt_size len
  exact ⟨by omega,twice,by omega,by omega⟩

#print axioms guarded
end DuplicatePrefix.PositiveRootCopyBounds
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.PositiveRootCopyBounds.guarded) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved guarded copy bounds dependency {dependency}"
