import duplicate_prefix.DuplicatePrefixCallbackAuthorization

namespace DuplicatePrefix.DuplicatePrefixCallbackVisitAuthorization
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallbackAuthorization

/-- Entry-side data query. A missing or Either classification does not skip
the node: the real visitor descends and recomputes classification afterwards. -/
def entrySkip (state : LocationState) (kind : AccessKind) :
    Option WildcardAccessRelatedness → Bool
  | some .LocalAccess => skip state kind .LocalAccess
  | some .ForeignAccess => skip state kind .ForeignAccess
  | some .EitherAccess | none => false

/-- Raw authorization for the pair of classifications before and after child
processing. The pairs will be supplied by contributor-set arithmetic, not by
assuming any operation succeeds. If entry did not skip, an exact EXIT query
must recurse: permitting a new skip there would make recordNewAccess fail.
This is a two-query component specification, not complete reference validity. -/
def Authorized (state : LocationState) (kind : AccessKind) (held : Bool)
    (entry exit : Option WildcardAccessRelatedness) : Prop :=
  state.possible = true ∧ (entrySkip state kind entry = true ∨
    match exit with
    | none => False
    | some .EitherAccess => True
    | some .LocalAccess => skip state kind .LocalAccess = false ∧
        DuplicatePrefixScalarAuthorization.Compatible state kind .LocalAccess held
    | some .ForeignAccess => skip state kind .ForeignAccess = false ∧
        DuplicatePrefixScalarAuthorization.Compatible state kind .ForeignAccess held)

/-- Entry skipping agrees with the source's optional exact-relatedness branch.
The query is independent of scalar operation success. -/
theorem entry_skip_source (state : LocationState) (kind : AccessKind)
    (entry : Option WildcardAccessRelatedness) :
    entrySkip state kind entry = true ↔
      ∃ related exact, entry = some related ∧ exactRelation related = some exact ∧
        state.skipIfKnownNoop kind exact = .SkipSelfAndChildren := by
  cases entry with
  | none => simp [entrySkip]
  | some related =>
    cases related <;> simp [entrySkip, exactRelation, skip_source]

theorem exact_transition (state : LocationState) (kind : AccessKind) (held : Bool)
    (exact : AccessRelatedness) (possible : state.possible = true)
    (notSkipped : skip state kind exact = false)
    (compatible : DuplicatePrefixScalarAuthorization.Compatible state kind exact held) :
    ∃ recorded next delta, state.recordNewAccess kind exact = .Recorded recorded ∧
      recorded.performAccess kind exact held = .Success next delta := by
  have recurse : state.skipIfKnownNoop kind exact = .Recurse := by
    cases equality : state.skipIfKnownNoop kind exact with
    | Recurse => rfl
    | SkipSelfAndChildren =>
      have skipped := (skip_source state kind exact).mpr equality
      simp [notSkipped] at skipped
  let recorded := {state with idempotentForeignAccess := (
    IdempotentForeignAccess.recordNew state.idempotentForeignAccess
      (IdempotentForeignAccess.fromAccessAndRelatedness kind exact))}
  have inherited : DuplicatePrefixScalarAuthorization.Compatible recorded kind exact held := by
    cases kind <;> cases exact <;> exact compatible
  have possibleRecorded : recorded.possible = true := possible
  obtain ⟨next, delta, access⟩ :=
    (DuplicatePrefixScalarAuthorization.compatible_iff recorded kind exact held possibleRecorded).mp inherited
  exact ⟨recorded, next, delta,
    by simp [LocationState.recordNewAccess, recurse, recorded], access⟩

/-- The exact record-and-transition branch after a non-skipped entry is
derived from the raw two-query contract. No final activity or successful
record/transition occurs among its premises. -/
theorem exit_transition (state : LocationState) (kind : AccessKind) (held : Bool)
    (entry exit : Option WildcardAccessRelatedness)
    (authorized : Authorized state kind held entry exit)
    (notSkipped : entrySkip state kind entry = false) :
    ∃ related, exit = some related ∧
      (related = .EitherAccess ∨ ∃ exact recorded next delta,
        exactRelation related = some exact ∧
        state.recordNewAccess kind exact = .Recorded recorded ∧
        recorded.performAccess kind exact held = .Success next delta) := by
  have branch := authorized.2.resolve_left (by simp [notSkipped])
  cases exit with
  | none => exact False.elim branch
  | some related =>
    refine ⟨related, rfl, ?_⟩
    cases related with
    | EitherAccess => exact .inl rfl
    | LocalAccess =>
      obtain ⟨recorded, next, delta, record, access⟩ :=
        exact_transition state kind held .LocalAccess authorized.1 branch.1 branch.2
      exact .inr ⟨.LocalAccess, recorded, next, delta, rfl, record, access⟩
    | ForeignAccess =>
      obtain ⟨recorded, next, delta, record, access⟩ :=
        exact_transition state kind held .ForeignAccess authorized.1 branch.1 branch.2
      exact .inr ⟨.ForeignAccess, recorded, next, delta, rfl, record, access⟩

end DuplicatePrefix.DuplicatePrefixCallbackVisitAuthorization
