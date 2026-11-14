import Miri.Input.TraitSelection.ScopedEnvironmentEntailment
namespace Miri.Input.TraitSelection.ScopedEnvironmentEntailment
open GenericSubstitution
private def p (universeIndex : Nat) : Term := .placeholder .type universeIndex 0 .anonymous
private def obligation (identity : DefinitionIdentity) (self : Term) : Clause :=
  ⟨#[],.trait ⟨.positive,⟨identity,#[self]⟩⟩⟩
private def success (result : Except String (Option EnvironmentEntailment.Derivation)) : Bool :=
  match result with | .ok (some _) => true | _ => false
private def declarationForTest (identity : DefinitionIdentity) (supers : Array Clause) : TraitDeclaration :=
  ⟨identity,#[.type],false,false,false,false,false,none,supers,#[],#[]⟩
private def source : Program := {traits := #[declarationForTest ⟨0,1⟩ #[obligation ⟨0,2⟩ (.parameter .type 0)],
  declarationForTest ⟨0,2⟩ #[]]}
example : success (entails source 1 #[obligation ⟨0,1⟩ (p 1)] 30 (obligation ⟨0,1⟩ (p 1))) = true := by decide +kernel
example : success (entails source 1 #[obligation ⟨0,1⟩ (p 1)] 30 (obligation ⟨0,2⟩ (p 1))) = true := by decide +kernel
example : success (entails source 0 #[obligation ⟨0,1⟩ (p 1)] 30 (obligation ⟨0,1⟩ (p 1))) = false := by decide +kernel
example : success (entails source 1 #[obligation ⟨0,1⟩ (p 2)] 30 (obligation ⟨0,1⟩ (p 2))) = false := by decide +kernel
private def malformedSource : Program := {traits := #[declarationForTest ⟨0,1⟩ #[obligation ⟨0,2⟩ (p 1)],
  declarationForTest ⟨0,2⟩ #[]]}
example : success (entails malformedSource 1 #[obligation ⟨0,1⟩ (p 1)] 30 (obligation ⟨0,2⟩ (p 1))) = false := by decide +kernel
end Miri.Input.TraitSelection.ScopedEnvironmentEntailment
