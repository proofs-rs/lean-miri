import duplicate_prefix.DuplicatePrefixCallbackVisitAuthorization

namespace DuplicatePrefix.S02SifaQueryWeakening
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization DuplicatePrefixCallbackVisitAuthorization
set_option autoImplicit false

/-- Weakening the SIFA cache cannot introduce a foreign skip. -/
theorem skip_false_weaken (state : LocationState) (strongest : IdempotentForeignAccess)
    (kind : AccessKind) (related : AccessRelatedness)
    (initial : skip state kind related = false) :
    skip {state with idempotentForeignAccess :=
      (state.idempotentForeignAccess.ensureNoStrongerThan strongest).1} kind related = false := by
  rcases state with ⟨permission,accessed,cache⟩
  cases cache <;> cases strongest <;> cases kind <;> cases related <;>
    simp_all [skip,IdempotentForeignAccess.ensureNoStrongerThan,
      IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.fromForeign,
      IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
      IdempotentForeignAccess.rank,AccessRelatedness.isForeign]

/-- The only entry classification that can lose certification from cache
weakening is Foreign. Local, Either and missing entry classifications already
require the exit branch, whose non-skip condition is preserved. This is a scalar
query lemma; constructor contributor geometry must supply its entry condition. -/
theorem authorized_weaken_of_entry_not_foreign
    (state : LocationState) (strongest : IdempotentForeignAccess)
    (kind : AccessKind) (held : Bool)
    (entry exit : Option WildcardAccessRelatedness)
    (notForeign : entry ≠ some .ForeignAccess)
    (initial : Authorized state kind held entry exit) :
    Authorized {state with idempotentForeignAccess :=
      (state.idempotentForeignAccess.ensureNoStrongerThan strongest).1}
      kind held entry exit := by
  have entryFalse : entrySkip state kind entry = false := by
    cases entry with
    | none => rfl
    | some entry => cases entry <;> simp_all [entrySkip,skip,AccessRelatedness.isForeign]
  have nextEntryFalse : entrySkip {state with idempotentForeignAccess :=
      (state.idempotentForeignAccess.ensureNoStrongerThan strongest).1} kind entry = false := by
    cases entry with
    | none => rfl
    | some entry => cases entry <;> simp_all [entrySkip,skip,AccessRelatedness.isForeign]
  have possible : ({state with idempotentForeignAccess :=
      (state.idempotentForeignAccess.ensureNoStrongerThan strongest).1} : LocationState).possible = state.possible := rfl
  refine ⟨possible.trans initial.1,Or.inr ?_⟩
  have branch := initial.2.resolve_left (by simp [entryFalse])
  cases exit with
  | none => exact branch
  | some exit =>
    cases exit with
    | EitherAccess => trivial
    | LocalAccess =>
      refine ⟨skip_false_weaken state strongest kind .LocalAccess branch.1,?_⟩
      cases kind <;> exact branch.2
    | ForeignAccess =>
      refine ⟨skip_false_weaken state strongest kind .ForeignAccess branch.1,?_⟩
      cases kind <;> exact branch.2

/-- Shared-child cache weakening to Read preserves every Read callback query,
including entry Foreign skips. The remaining constructor obstruction is Write. -/
theorem authorized_read_weaken_read_iff
    (state : LocationState) (held : Bool)
    (entry exit : Option WildcardAccessRelatedness) :
    Authorized {state with idempotentForeignAccess :=
      (state.idempotentForeignAccess.ensureNoStrongerThan .Read).1}
      .Read held entry exit ↔ Authorized state .Read held entry exit := by
  rcases state with ⟨permission,accessed,cache⟩
  cases cache <;>
    simp [Authorized,entrySkip,skip,IdempotentForeignAccess.ensureNoStrongerThan,
      IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.fromForeign,
      IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
      IdempotentForeignAccess.rank,LocationState.possible,
      DuplicatePrefixScalarAuthorization.Compatible,
      GeneralBorrowProtectedReadCompatible.Compatible]

end DuplicatePrefix.S02SifaQueryWeakening

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02SifaQueryWeakening.skip_false_weaken,
      ``DuplicatePrefix.S02SifaQueryWeakening.authorized_read_weaken_read_iff,
      ``DuplicatePrefix.S02SifaQueryWeakening.authorized_weaken_of_entry_not_foreign] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
