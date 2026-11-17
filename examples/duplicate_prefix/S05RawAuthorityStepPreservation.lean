import duplicate_prefix.OrdinaryBorrowAuthority
import duplicate_prefix.GeneralBorrowExposedConditionalWritePermissions
import duplicate_prefix.GeneralBorrowExposedVirtualSchedule

/-! Fixed-source scalar authority is preserved by matching actual accesses.
Write reuses the existing source permission-table theorem; Read retains the
stronger mutable-authority clauses. No representation preorder is introduced.
Materialization already preserves effective states in
GeneralBorrowExposedVirtualSchedule.materialized_effective; Either is scalar
identity. These facts do not supply tree traversal or recording success. -/
namespace DuplicatePrefix.S05RawAuthorityStepPreservation
open Miri.TreeBorrows Miri.TreeBorrows.Tree OrdinaryBorrowAuthority
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem local_read (state : LocationState) (held : Bool) (initial : LocalWrite state held) :
    ∃ next delta, state.performAccess .Read .LocalAccess held = .Success next delta ∧ LocalWrite next held := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission <;> try (rename_i conflicted; cases conflicted)
  all_goals cases accessed <;> cases held
  all_goals simp [LocalWrite,LocationState.possible,Permission.isUnique] at initial
  all_goals refine ⟨_,_,rfl,?_⟩
  all_goals simp_all [LocalWrite,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign]

private theorem foreign_read (state : LocationState) (held : Bool) (initial : ForeignWrite state held) :
    ∃ next delta, state.performAccess .Read .ForeignAccess held = .Success next delta ∧ ForeignWrite next held := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission <;> try (rename_i conflicted; cases conflicted)
  all_goals cases accessed <;> cases held
  all_goals simp [ForeignWrite,LocationState.possible,Permission.isUnique] at initial
  all_goals refine ⟨_,_,rfl,?_⟩
  all_goals simp_all [ForeignWrite,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign]

theorem local_step (state : LocationState) (held : Bool) (kind : AccessKind)
    (initial : LocalWrite state held) :
    ∃ next delta, state.performAccess kind .LocalAccess held = .Success next delta ∧ LocalWrite next held := by
  cases kind with
  | Read => exact local_read state held initial
  | Write =>
    obtain ⟨next,delta,step,compatible,_,_⟩ :=
      GeneralBorrowExposedConditionalWritePermissions.transition state .LocalAccess held initial
    exact ⟨next,delta,step,compatible⟩

theorem foreign_step (state : LocationState) (held : Bool) (kind : AccessKind)
    (initial : ForeignWrite state held) :
    ∃ next delta, state.performAccess kind .ForeignAccess held = .Success next delta ∧ ForeignWrite next held := by
  cases kind with
  | Read => exact foreign_read state held initial
  | Write =>
    obtain ⟨next,delta,step,compatible,_,_⟩ :=
      GeneralBorrowExposedConditionalWritePermissions.transition state .ForeignAccess held initial
    exact ⟨next,delta,step,compatible⟩

/-- Successful recording changes only SIFA. Recording admissibility remains
the responsibility of the actual visitor's recurse/skip proof. -/
theorem record_fields (state recorded : LocationState) (kind : AccessKind) (relation : AccessRelatedness)
    (record : state.recordNewAccess kind relation = .Recorded recorded) :
    recorded.permission = state.permission ∧ recorded.accessed = state.accessed := by
  unfold LocationState.recordNewAccess at record
  split at record
  · cases record
    exact ⟨rfl,rfl⟩
  · cases record

theorem record_local (state recorded : LocationState) (held : Bool)
    (kind : AccessKind) (relation : AccessRelatedness) (initial : LocalWrite state held)
    (record : state.recordNewAccess kind relation = .Recorded recorded) : LocalWrite recorded held := by
  obtain ⟨permission,accessed⟩ := record_fields state recorded kind relation record
  simpa only [LocalWrite,LocationState.possible,permission,accessed] using initial

theorem record_foreign (state recorded : LocationState) (held : Bool)
    (kind : AccessKind) (relation : AccessRelatedness) (initial : ForeignWrite state held)
    (record : state.recordNewAccess kind relation = .Recorded recorded) : ForeignWrite recorded held := by
  obtain ⟨permission,accessed⟩ := record_fields state recorded kind relation record
  simpa only [ForeignWrite,LocationState.possible,permission,accessed] using initial

end DuplicatePrefix.S05RawAuthorityStepPreservation

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05RawAuthorityStepPreservation." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved raw authority step dependency {dependency}"
