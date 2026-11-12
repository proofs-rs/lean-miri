import Miri.Input.TraitSelection.EnvironmentEntailment

open Miri.Input.GenericSubstitution Miri.Input.TraitSelection
open Miri.Input.TraitSelection.EnvironmentEntailment
private def sized : DefinitionIdentity := ⟨1,1⟩
private def bounded : DefinitionIdentity := ⟨1,2⟩
private def metaSized : DefinitionIdentity := ⟨1,3⟩
private def parameter : Term := .parameter .type 0
private def obligation (id : DefinitionIdentity) (term : Term := parameter) : Clause :=
  ⟨#[],.trait ⟨.positive,⟨id,#[term]⟩⟩⟩
private def declaration (id : DefinitionIdentity) (supers : Array Clause := #[]) : TraitDeclaration := {
  definition := id, parameters := #[.type], isAuto := false, isAlias := false,
  isUnsafe := false, isCoinductive := false, isMarker := false, langItem := none,
  superPredicates := supers, implementations := #[] }
private def program : Program := {traits := #[declaration sized,
  declaration bounded #[obligation sized],declaration metaSized]}
private def classification : Except String (Option Derivation) → String
  | .error _ => "error" | .ok none => "unknown" | .ok (some _) => "proved"
example : classification (entails program #[.type] #[obligation sized] 30 (obligation sized)) = "proved" := by decide +kernel
example : classification (entails program #[.type] #[obligation bounded] 30 (obligation sized)) = "proved" := by decide +kernel
example : classification (entails program #[.type] #[obligation metaSized] 30 (obligation sized)) = "unknown" := by decide +kernel
example : classification (entails program #[.type] #[⟨#[],.trait ⟨.negative,⟨bounded,#[parameter]⟩⟩⟩] 30 (obligation sized)) = "unknown" := by decide +kernel
example : classification (entails program #[.type] #[obligation ⟨9,9⟩] 30 (obligation sized)) = "error" := by decide +kernel
example : classification (entails program #[.type] #[obligation bounded (.parameter .type 1)] 30 (obligation sized)) = "error" := by decide +kernel
example : classification (entails program #[.type] #[obligation bounded] 0 (obligation sized)) = "error" := by decide +kernel
example : classification (entails {traits := #[declaration bounded #[obligation bounded]]}
    #[.type] #[obligation bounded] 30 (obligation sized)) = "unknown" := by decide +kernel
