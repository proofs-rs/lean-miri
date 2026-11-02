import duplicate_prefix.GeneralBorrowPermissions
namespace DuplicatePrefix.GeneralBorrowSifaPermissionConsistency
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPermissions
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A recorded foreign skip strength is bounded by the current permission's
actual idempotent foreign strength under the current protection bit. This is
separate from possible/ownership and must be formed from actual history. -/
def Consistent (state : LocationState) (held : Bool) : Prop :=
  ∃ strongest, state.permission.strongestIdempotentForeignAccess held = .Access strongest ∧
    state.idempotentForeignAccess.rank ≤ strongest.rank

/-- Protected unconflicted reservations cannot soundly cache a foreign Read
skip. This forces the real visitor to recurse rather than silently prune it. -/
theorem reservation_recurse (state : LocationState) (consistent : Consistent state true)
    (reservation : state.permission = .ReservedFrz false) :
    state.idempotentForeignAccess = .None ∧ state.skipIfKnownNoop .Read .ForeignAccess = .Recurse := by
  obtain ⟨strongest,strongestEq,bound⟩ := consistent
  rw [reservation] at strongestEq
  have same : strongest = .None := by
    change Permission.IdempotentAccessResult.Access .None = .Access strongest at strongestEq
    exact (Permission.IdempotentAccessResult.Access.inj strongestEq).symm
  subst strongest
  have none : state.idempotentForeignAccess = .None := by
    cases sifa : state.idempotentForeignAccess <;> simp_all [IdempotentForeignAccess.rank]
  refine ⟨none,?_⟩
  simp only [LocationState.skipIfKnownNoop,AccessRelatedness.isForeign,none,reservation,
    IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.canSkipForeignAccess,
    IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,IdempotentForeignAccess.rank,
    Permission.isDisabled,Permission.isFrozen]
  rfl

/-- Actual newly-created protected Default reservations form this scalar
invariant with SIFA.None. Accessed and lazy states are both allowed. -/
theorem protected_reservation (accessed : Bool) : Consistent ⟨.ReservedFrz false,accessed,.None⟩ true :=
  ⟨.None,rfl,Nat.le_refl _⟩

theorem unprotected_reservation (accessed : Bool) : Consistent ⟨.ReservedFrz false,accessed,.Read⟩ false :=
  ⟨.Read,rfl,Nat.le_refl _⟩

theorem frozen (accessed held : Bool) : Consistent ⟨.Frozen,accessed,.Read⟩ held :=
  ⟨.Read,rfl,Nat.le_refl _⟩

theorem unique (accessed held : Bool) : Consistent ⟨.Unique,accessed,.None⟩ held :=
  ⟨.None,rfl,Nat.le_refl _⟩

/-- Public-dispatch equations for the fixed source permission rules. -/
private theorem local_read_rule (permission : Permission) (held : Bool) :
    performAccess .Read .LocalAccess permission held = match permission with
      | .Disabled => .UndefinedBehavior | readable => .Transition readable := rfl
private theorem foreign_read_rule (permission : Permission) (held : Bool) :
    performAccess .Read .ForeignAccess permission held = match permission with
      | .Cell => .Transition .Cell | .Frozen => .Transition .Frozen | .Disabled => .Transition .Disabled
      | .ReservedFrz _ => if held then .Transition (.ReservedFrz true) else .Transition permission
      | .ReservedIM => if held then .ImpossibleProtectedReservedIM else .Transition .ReservedIM
      | .Unique => if held then .Transition .Disabled else .Transition .Frozen := rfl
private theorem local_write_rule (permission : Permission) (held : Bool) :
    performAccess .Write .LocalAccess permission held = match permission with
      | .Cell => .Transition .Cell
      | .ReservedFrz true => if held then .UndefinedBehavior else .Transition .Unique
      | .ReservedFrz false | .ReservedIM | .Unique => .Transition .Unique
      | .Frozen | .Disabled => .UndefinedBehavior := rfl
private theorem foreign_write_rule (permission : Permission) (held : Bool) :
    performAccess .Write .ForeignAccess permission held = match permission with
      | .Cell => .Transition .Cell
      | .ReservedIM => if held then .ImpossibleProtectedReservedIM else .Transition .ReservedIM
      | _ => .Transition .Disabled := rfl

macro "simplify_consistency_pipeline" : tactic => `(tactic| simp_all [Consistent,Permission.strongestIdempotentForeignAccess,
    IdempotentForeignAccess.rank,LocationState.recordNewAccess,LocationState.skipIfKnownNoop,
    IdempotentForeignAccess.fromAccessAndRelatedness,IdempotentForeignAccess.fromForeign,
    IdempotentForeignAccess.canSkipForeignAccess,IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,
    IdempotentForeignAccess.recordNew,IdempotentForeignAccess.max,LocationState.performAccess,
    performAccessTransition,local_read_rule,foreign_read_rule,local_write_rule,foreign_write_rule,
    AccessRelatedness.isForeign,PermTransition.applied,PermTransition.isNoop,
    Permission.isDisabled,Permission.isFrozen,Permission.isUnique,LocationState.possible])

/-- The real record-then-access node pipeline preserves permission/SIFA
consistency on success. This component consumes its actual intermediate
source equations; the ownership-derived visitor theorem below supplies them. -/
theorem pipeline (state recorded next : LocationState) (transition : PermTransition)
    (kind : AccessKind) (related : AccessRelatedness) (held : Bool)
    (initial : Consistent state held)
    (record : state.recordNewAccess kind related = .Recorded recorded)
    (success : recorded.performAccess kind related held = .Success next transition) : Consistent next held := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases held <;> cases kind <;> cases related <;>
      (simplify_consistency_pipeline
       all_goals subst_vars
       all_goals simplify_consistency_pipeline
       all_goals try obtain ⟨stateEq,transitionEq⟩ := success
       all_goals subst_vars
       all_goals simplify_consistency_pipeline)
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases held <;> cases kind <;> cases related <;>
      (simplify_consistency_pipeline
       all_goals subst_vars
       all_goals simplify_consistency_pipeline
       all_goals try obtain ⟨stateEq,transitionEq⟩ := success
       all_goals subst_vars
       all_goals simplify_consistency_pipeline)

/-- Ownership derives the actual visitor's successful branch, and both the
real skip and record/access branches preserve the formed scalar invariant.
Successful record/access equations are outputs rather than premises. -/
theorem visit (state : LocationState) (kind : AccessKind) (related : AccessRelatedness) (held : Bool)
    (owned : AccessOwned state kind related held) (initial : Consistent state held) :
    (state.skipIfKnownNoop kind related = .SkipSelfAndChildren ∧ Consistent state held) ∨
    ∃ recorded next transition,
      state.recordNewAccess kind related = .Recorded recorded ∧
      recorded.performAccess kind related held = .Success next transition ∧
      AccessOwned next kind related held ∧ Consistent next held := by
  rcases GeneralBorrowPermissions.visit_for_success state kind related held owned with skip | ⟨recorded,next,transition,record,success,preserved⟩
  · exact .inl ⟨skip,initial⟩
  · exact .inr ⟨recorded,next,transition,record,success,preserved,pipeline state recorded next transition kind related held initial record success⟩

/-- A skip licensed by a formed permission/SIFA invariant is an actual
idempotent permission transition, including the disabled/frozen skip cases. -/
theorem skip_permission (state : LocationState) (kind : AccessKind) (held : Bool)
    (initial : Consistent state held) (skip : state.skipIfKnownNoop kind .ForeignAccess = .SkipSelfAndChildren) :
    performAccessTransition kind .ForeignAccess state.permission held = .Transition ⟨state.permission,state.permission⟩ := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases held <;> cases kind <;>
      simplify_consistency_pipeline
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases held <;> cases kind <;>
      simplify_consistency_pipeline

/-- The actual constructor's ensureNoStrongerThan update only weakens
recorded SIFA, so it preserves the permission bound without an access premise. -/
theorem weaken (state : LocationState) (held : Bool) (strongestAllowed : IdempotentForeignAccess)
    (initial : Consistent state held) :
    Consistent {state with idempotentForeignAccess := (state.idempotentForeignAccess.ensureNoStrongerThan strongestAllowed).1} held := by
  obtain ⟨strongest,permission,bound⟩ := initial
  refine ⟨strongest,permission,?_⟩
  have weaker : (state.idempotentForeignAccess.ensureNoStrongerThan strongestAllowed).1.rank ≤ state.idempotentForeignAccess.rank := by
    cases state.idempotentForeignAccess <;> cases strongestAllowed <;> decide
  exact Nat.le_trans weaker bound

/-- Protector removal cannot invalidate the scalar permission/SIFA bound. -/
theorem unprotect (state : LocationState) (initial : Consistent state true) : Consistent state false := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> simp_all [Consistent,Permission.strongestIdempotentForeignAccess,IdempotentForeignAccess.rank]
    all_goals omega
  | ReservedIM =>
    obtain ⟨strongest,impossible,_⟩ := initial
    cases impossible
  | Cell | Unique | Frozen | Disabled =>
    simpa only [Consistent,Permission.strongestIdempotentForeignAccess] using initial

/-- A clean vacant projection uses Disabled with no recorded foreign access. -/
theorem vacant (held : Bool) : Consistent ⟨.Disabled,false,.None⟩ held :=
  ⟨.Write,rfl,by decide⟩

end DuplicatePrefix.GeneralBorrowSifaPermissionConsistency
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowSifaPermissionConsistency.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved SIFA/permission consistency dependency {dependency}"
