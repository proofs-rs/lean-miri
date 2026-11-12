import Miri.MIR.Fold
open Miri.MIR
namespace MirFoldChecks

example (source : ProjectionElem) : Fold.projection Fold.identity source = .ok source := by
  cases source <;> rfl
example (source : GenericArg) : Fold.genericArg Fold.identity source = .ok source := by
  cases source <;> rfl

private def hooks : Fold.Hooks := { Fold.identity with ty := fun id => pure (id + 100) }
private def pointer : ConstValue := .Scalar (.Ptr (.Allocation 37 8 true false))
private def constant : ConstOperand := ⟨⟨19⟩,some 3,.Val pointer 2⟩
-- Substitution of a constant's type does not mutate its allocation identity,
-- offset, provenance flags, span or user annotation.
example : Fold.constantOperand hooks constant = .ok ⟨⟨19⟩,some 3,.Val pointer 102⟩ := by rfl

private def missing : Fold.Hooks := { Fold.identity with ty := fun _ => .error "type unavailable" }
private def projected : Place := ⟨1,#[.Deref,.Field 2 7,.OpaqueCast 9]⟩
example : Fold.operand missing (.Copy projected) = .error "type unavailable" := by
  simp [Fold.operand, Fold.place, Fold.projection, projected, missing, Fold.identity]
  rfl

end MirFoldChecks
