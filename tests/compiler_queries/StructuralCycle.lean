import Miri.Input.TraitSelection.StructuralCycle

open Miri.Input.GenericSubstitution Miri.Input.TraitSelection
private def identity : DefinitionIdentity := ⟨0,1⟩
private def node : Term := .definition .type "adt" ⟨0,2⟩ .nil
private def goal : Goal := ⟨.positive,⟨identity,#[node]⟩⟩
private def source : TraitDeclaration := {
  definition := identity, parameters := #[.type], isAuto := true,
  isAlias := false, isUnsafe := false, isCoinductive := true,
  isMarker := false, langItem := none, superPredicates := #[], implementations := #[] }
private def classify (value : Except String (Option Nat)) : String :=
  match value with | .ok (some _) => "certified" | .ok none => "unknown" | .error _ => "error"
example : classify (StructuralCycle.certify {traits := #[source]} {} 30 #[goal] goal) = "certified" := by decide +kernel
example : classify (StructuralCycle.certify {traits := #[{source with isCoinductive := false}]} {} 30 #[goal] goal) = "unknown" := by decide +kernel
example : classify (StructuralCycle.certify {traits := #[{source with isAuto := false}]} {} 30 #[goal] goal) = "unknown" := by decide +kernel
example : classify (StructuralCycle.certify {traits := #[source]} {} 30 #[] goal) = "unknown" := by decide +kernel
example : classify (StructuralCycle.certify {traits := #[source]} {} 30 #[{goal with polarity := .negative}] {goal with polarity := .negative}) = "unknown" := by decide +kernel
private def negativeImpl : Impl := {
  definition := ⟨0,3⟩, parameters := #[], traitRef := goal.traitRef,
  polarity := .negative, isDefault := false, predicates := #[], associatedValues := #[] }
example : classify (StructuralCycle.certify {traits := #[{source with implementations := #[negativeImpl]}]} {} 30 #[goal] goal) = "unknown" := by decide +kernel

example : classify (StructuralCycle.certify {traits := #[source]} {} 30 #[goal] goal 1) = "unknown" := by decide +kernel
