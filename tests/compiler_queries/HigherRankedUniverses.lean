import Miri.Input.TraitSelection.Universes

open Miri.Input.GenericSubstitution Miri.Input.TraitSelection
open Miri.Input.TraitSelection.Universes
private def variables : Array BoundVariable := #[.region .anonymous,.type .anonymous,.constant]
private def region (depth position : Nat) : Term := .bound .region (.Bound depth) position .anonymous
private def rejected (value : Except String α) : Bool := match value with | .error _ => true | .ok _ => false
private def placeholder (universeIndex : Nat) : Term := .placeholder .region universeIndex 0 .anonymous
example : (enter 7).current = 8 := rfl
example : openTerm variables 8 10 0 (region 0 0) = .ok (placeholder 8) := by cbv
example : openTerm variables 8 10 0 (.binder #[.region .anonymous] (region 0 0)) =
    .ok (.binder #[.region .anonymous] (region 0 0)) := by cbv
example : openTerm variables 8 10 0 (.binder #[.region .anonymous] (region 1 0)) =
    .ok (.binder #[.region .anonymous] (placeholder 8)) := by cbv
example : openTerm variables 8 10 0 (.binder #[.region .anonymous] (region 2 0)) =
    .ok (.binder #[.region .anonymous] (region 1 0)) := by cbv
example : rejected (openTerm variables 8 10 0 (region 0 1)) = true := by cbv
example : rejected (openTerm variables 8 10 0 (region 0 3)) = true := by cbv
example : rejected (openTerm variables 8 10 0 (.bound .region .Canonical 0 .anonymous)) = true := by cbv
example : openTerm variables 8 10 0 (.bound .type (.Bound 0) 1 .anonymous) =
    .ok (.placeholder .type 8 1 .anonymous) := by cbv
example : openTerm variables 8 10 0 (.bound .constant (.Bound 0) 2 .anonymous) =
    .ok (.placeholder .constant 8 2 .anonymous) := by cbv
example : checkAssignable 8 10 (placeholder 8) = .ok () := by cbv
example : checkAssignable 9 10 (placeholder 8) = .ok () := by cbv
example : rejected (checkAssignable 7 10 (placeholder 8)) = true := by cbv
example : rejected (checkAssignable 7 10 (.node .type "tuple" "" (.ofArray #[placeholder 8]))) = true := by cbv
example : openClause (enter 7) 10 ⟨variables,.equal (region 0 0) (region 0 0)⟩ =
    .ok ⟨#[],.equal (placeholder 8) (placeholder 8)⟩ := by cbv
example : rejected (openClause ⟨7,7⟩ 10 ⟨variables,.equal (region 0 0) (region 0 0)⟩) = true := by cbv
