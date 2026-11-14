import Miri.Input.TraitSelection.Substitution

open Miri.Input.GenericSubstitution Miri.Input.TraitSelection
private def boolean : Term := .atom .type "bool" ""
private def source : Clause := ⟨#[.region .anonymous], .wellFormed (.parameter .type 0)⟩
private def escaping : Term := .bound .type (.Bound 0) 0 .anonymous

-- The surrounding predicate Binder shifts a substituted escaping bound type.
example : Substitution.clause 20 #[escaping] source =
    .ok ⟨#[.region .anonymous], .wellFormed (.bound .type (.Bound 1) 0 .anonymous)⟩ := by cbv
example : Substitution.clause 20 #[boolean]
    ⟨#[.type .anonymous], .equal (.bound .type (.Bound 0) 0 .anonymous) (.parameter .type 0)⟩ =
    .ok ⟨#[.type .anonymous], .equal (.bound .type (.Bound 0) 0 .anonymous) boolean⟩ := by cbv
example : Substitution.clause 20 #[boolean]
    ⟨#[], .hostEffect true ⟨⟨0,1⟩, #[.parameter .type 0]⟩⟩ =
    .ok ⟨#[], .hostEffect true ⟨⟨0,1⟩, #[boolean]⟩⟩ := by cbv
example : Substitution.clause 20 #[] ⟨#[], .unstableFeature "source_feature"⟩ =
    .ok ⟨#[], .unstableFeature "source_feature"⟩ := by cbv
example : Substitution.clause 20 #[.atom .region "erased" ""] source =
    .error "generic parameter argument sort mismatch" := by cbv
example : Substitution.clause 20 #[] source =
    .error "generic material has parameters but no arguments" := by cbv
example : Substitution.clause 0 #[boolean] source =
    .error "generic material substitution traversal exhausted" := by cbv
example : Substitution.clause 20 #[boolean]
    ⟨#[], .projection .projectionType ⟨0,1⟩ #[.parameter .type 0] (.parameter .type 0)⟩ =
    .ok ⟨#[], .projection .projectionType ⟨0,1⟩ #[boolean] boolean⟩ := by cbv
