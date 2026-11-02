import duplicate_prefix.ProtectorInsertion
import duplicate_prefix.ProtectedStages
import duplicate_prefix.ReferenceBorrowDriver
namespace DuplicatePrefix.AsMutOutputMask
open Miri Miri.Memory Miri.TreeBorrows Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem inserted (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (protections : ProtectedTags) (mask : ProtectedStages.StageMask tags protections 5 false) :
    ProtectedBorrowAccess.SixMask tags (protections.insert (tags 5) .StrongProtector) true := by
  intro i
  by_cases last : i = 5
  · subst i
    simp [ProtectedTags.contains]
  · have different : tags i ≠ tags 5 := fun h => last (distinct h)
    rw [ProtectorInsertion.contains_other protections (tags 5) (tags i) .StrongProtector different]
    have before := mask i (by have bound := i.isLt; have not5 : i.val ≠ 5 := fun h => last (Fin.ext h);omega)
    have beq5 : (i == 5) = false := Bool.eq_false_iff.mpr (fun h => last (beq_iff_eq.mp h))
    simpa [beq5] using before

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``inserted) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved asmut inserted protection mask dependency {dependency}"
end DuplicatePrefix.AsMutOutputMask
