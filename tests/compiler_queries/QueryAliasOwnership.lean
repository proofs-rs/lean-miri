import Miri.Input.QueryAliasScope

open Miri.Input GenericSubstitution TraitSelection QueryAliasScope

private def placeholder (universeIndex : Nat) : Term :=
  .placeholder .region universeIndex 0 .anonymous
private def sharedRef (region : Term) : Term :=
  .node .type "reference" "immutable" (.ofArray #[region, .atom .type "uint" "u8"])
private def succeeds (value : Except String Unit) : Bool :=
  match value with | .ok _ => true | .error _ => false

example : succeeds (requireOwned 1 100 (placeholder 1)) = true := by decide +kernel
example : succeeds (requireOwned 2 100 (placeholder 1)) = true := by decide +kernel
example : succeeds (requireOwned 2 100 (placeholder 2)) = true := by decide +kernel
example : succeeds (requireOwned 0 100 (placeholder 1)) = false := by decide +kernel
example : succeeds (requireOwned 1 100 (placeholder 0)) = false := by decide +kernel
example : succeeds (requireOwned 1 100 (placeholder 2)) = false := by decide +kernel
example : succeeds (requireOwned 1 100 (.placeholder .constant 1 0 (.named ⟨0,1⟩))) = false := by decide +kernel
example : succeeds (requireOwned 1 100 (.parameter .type 0)) = false := by decide +kernel
example : succeeds (requireOwned 1 100 (.inference .type 0)) = false := by decide +kernel
example : succeeds (HigherRankedMatch.validateSourceClause #[] 100
  ⟨#[], .equal (.placeholder .type 1 0 .anonymous) (.placeholder .type 1 0 .anonymous)⟩) = false := by decide +kernel


example : succeeds (requireOwned 1 100 (sharedRef (placeholder 1))) = true := by decide +kernel
example : succeeds (requireOwned 1 100 (sharedRef (placeholder 2))) = false := by decide +kernel
example : succeeds (requireOwned 1 100 (.bound .region (.Bound 0) 0 .anonymous)) = false := by decide +kernel
