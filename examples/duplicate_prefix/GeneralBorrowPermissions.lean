import Lean.Elab.Command
import Miri.TreeBorrows.NormalTree
namespace DuplicatePrefix.GeneralBorrowPermissions
open Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
/-- Data-only writable permission on the accessed node and its ancestors.
Protected conflicted reservations cannot be activated. -/
def LocalOwned (state : LocationState) (held : Bool) : Prop :=
  state.possible = true ∧ match state.permission with
  | .Cell | .Unique | .ReservedFrz false => True
  | .ReservedIM | .ReservedFrz true => held = false
  | .Frozen | .Disabled => False
/-- Data-only compatibility of a foreign node with exclusive access.
Inactive held children may be invalidated without violating their protector;
active held foreign borrows are excluded except Cell. -/
def ForeignOwned (state : LocationState) (held : Bool) : Prop :=
  state.possible = true ∧ (held = false ∨ state.permission = .Cell ∨
    (state.accessed = false ∧ state.permission ≠ .ReservedIM))
def Owned (state : LocationState) (related : AccessRelatedness) (held : Bool) : Prop :=
  match related with
  | .LocalAccess => LocalOwned state held
  | .ForeignAccess => ForeignOwned state held

theorem access_success (state : LocationState) (related : AccessRelatedness)
    (held : Bool) (kind : AccessKind) (owned : Owned state related held) :
    ∃ next transition, state.performAccess kind related held = .Success next transition ∧
      Owned next related held := by
  rcases state with ⟨permission, accessed, sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases related <;> cases held <;> cases kind <;>
      (simp [Owned, LocalOwned, ForeignOwned, LocationState.possible, Permission.isUnique] at owned) <;>
      (refine ⟨_, _, rfl, ?_⟩; simp [Owned, LocalOwned, ForeignOwned, LocationState.possible, Permission.isUnique, AccessRelatedness.isForeign])
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases related <;> cases held <;> cases kind <;>
      (simp [Owned, LocalOwned, ForeignOwned, LocationState.possible, Permission.isUnique] at owned) <;>
      (refine ⟨_, _, rfl, ?_⟩; simp [Owned, LocalOwned, ForeignOwned, LocationState.possible, Permission.isUnique, AccessRelatedness.isForeign])
/-- The real skip/record/access node pipeline is total under data ownership.
There are no successful-operation premises. -/
theorem visit_success (state : LocationState) (related : AccessRelatedness)
    (held : Bool) (kind : AccessKind) (owned : Owned state related held) :
    state.skipIfKnownNoop kind related = .SkipSelfAndChildren ∨
    ∃ recorded next transition,
      state.recordNewAccess kind related = .Recorded recorded ∧
      recorded.performAccess kind related held = .Success next transition ∧
      Owned next related held := by
  cases skip : state.skipIfKnownNoop kind related with
  | SkipSelfAndChildren => exact .inl rfl
  | Recurse =>
    let recorded := {state with idempotentForeignAccess := (
      IdempotentForeignAccess.recordNew state.idempotentForeignAccess
        (IdempotentForeignAccess.fromAccessAndRelatedness kind related))}
    have inherited : Owned recorded related held := by
      cases related <;> exact owned
    obtain ⟨next, transition, access, preserved⟩ := access_success recorded related held kind inherited
    exact .inr ⟨recorded,next,transition, by simp [LocationState.recordNewAccess,skip,recorded], access,preserved⟩

/-- Dropping a protector does not invalidate exclusive compatibility. -/
theorem owned_release (state : LocationState) (related : AccessRelatedness)
    (before after : Bool) (weaken : after = true → before = true)
    (owned : Owned state related before) : Owned state related after := by
  cases before <;> cases after <;> cases related <;>
    simp_all [Owned,LocalOwned,ForeignOwned]
  all_goals split at owned <;> simp_all

/-- Read permission on the shared accessed node and its ancestors. -/
def LocalReadable (state : LocationState) : Prop :=
  state.possible = true ∧ state.permission ≠ .Disabled

theorem local_read_success (state : LocationState) (held : Bool)
    (readable : LocalReadable state) :
    ∃ next transition, state.performAccess .Read .LocalAccess held = .Success next transition ∧
      LocalReadable next := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases held <;>
      (simp [LocalReadable,LocationState.possible,Permission.isUnique] at readable) <;>
      (refine ⟨_,_,rfl,?_⟩; simp [LocalReadable,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign])
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases held <;>
      (simp [LocalReadable,LocationState.possible,Permission.isUnique] at readable) <;>
      (refine ⟨_,_,rfl,?_⟩; simp [LocalReadable,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign])

theorem fresh_shared_readable (sifa : IdempotentForeignAccess) (accessed : Bool) :
    LocalReadable ⟨.Frozen,accessed,sifa⟩ := by
  simp [LocalReadable,LocationState.possible,Permission.isUnique]

theorem fresh_mutable_owned (sifa : IdempotentForeignAccess) (accessed held : Bool) :
    LocalOwned ⟨.ReservedFrz false,accessed,sifa⟩ held := by
  cases accessed <;> cases held <;> trivial

/-- Access-specific ownership permits a shared Frozen node on a read path. -/
def AccessOwned (state : LocationState) (kind : AccessKind)
    (related : AccessRelatedness) (held : Bool) : Prop :=
  match kind, related with
  | .Read, .LocalAccess => LocalReadable state
  | _, _ => Owned state related held

theorem access_for_success (state : LocationState) (kind : AccessKind)
    (related : AccessRelatedness) (held : Bool) (owned : AccessOwned state kind related held) :
    ∃ next transition, state.performAccess kind related held = .Success next transition ∧
      AccessOwned next kind related held := by
  cases kind <;> cases related
  · exact local_read_success state held owned
  · exact access_success state .ForeignAccess held .Read owned
  · exact access_success state .LocalAccess held .Write owned
  · exact access_success state .ForeignAccess held .Write owned

theorem visit_for_success (state : LocationState) (kind : AccessKind)
    (related : AccessRelatedness) (held : Bool) (owned : AccessOwned state kind related held) :
    state.skipIfKnownNoop kind related = .SkipSelfAndChildren ∨
    ∃ recorded next transition,
      state.recordNewAccess kind related = .Recorded recorded ∧
      recorded.performAccess kind related held = .Success next transition ∧
      AccessOwned next kind related held := by
  cases skip : state.skipIfKnownNoop kind related with
  | SkipSelfAndChildren => exact .inl rfl
  | Recurse =>
    let recorded := {state with idempotentForeignAccess := (
      IdempotentForeignAccess.recordNew state.idempotentForeignAccess
        (IdempotentForeignAccess.fromAccessAndRelatedness kind related))}
    have inherited : AccessOwned recorded kind related held := by
      cases kind <;> cases related <;> exact owned
    obtain ⟨next, transition, access, preserved⟩ := access_for_success recorded kind related held inherited
    exact .inr ⟨recorded,next,transition, by simp [LocationState.recordNewAccess,skip,recorded], access,preserved⟩

/-- Per-node ownership strength. Mutable ancestors retain write ownership
while a temporary shared leaf needs only read ownership. -/
def Required (state : LocationState) (writable : Bool)
    (related : AccessRelatedness) (held : Bool) : Prop :=
  if writable then Owned state related held else AccessOwned state .Read related held

theorem required_success (state : LocationState) (writable : Bool) (kind : AccessKind)
    (related : AccessRelatedness) (held : Bool) (allowed : writable = false → related = .LocalAccess → kind = .Read)
    (owned : Required state writable related held) :
    ∃ next transition, state.performAccess kind related held = .Success next transition ∧
      Required next writable related held := by
  cases writable with
  | true => exact access_success state related held kind owned
  | false =>
    cases related with
    | LocalAccess =>
      have read := allowed rfl rfl
      subst kind
      exact access_for_success state .Read .LocalAccess held owned
    | ForeignAccess => exact access_success state .ForeignAccess held kind owned

theorem required_visit (state : LocationState) (writable : Bool) (kind : AccessKind)
    (related : AccessRelatedness) (held : Bool) (allowed : writable = false → related = .LocalAccess → kind = .Read)
    (owned : Required state writable related held) :
    state.skipIfKnownNoop kind related = .SkipSelfAndChildren ∨
    ∃ recorded next transition,
      state.recordNewAccess kind related = .Recorded recorded ∧
      recorded.performAccess kind related held = .Success next transition ∧
      Required next writable related held := by
  cases skip : state.skipIfKnownNoop kind related with
  | SkipSelfAndChildren => exact .inl rfl
  | Recurse =>
    let recorded := {state with idempotentForeignAccess := (
      IdempotentForeignAccess.recordNew state.idempotentForeignAccess
        (IdempotentForeignAccess.fromAccessAndRelatedness kind related))}
    have inherited : Required recorded writable related held := by
      cases writable <;> cases related <;> exact owned
    obtain ⟨next, transition, access, preserved⟩ := required_success recorded writable kind related held allowed inherited
    exact .inr ⟨recorded,next,transition, by simp [LocationState.recordNewAccess,skip,recorded], access,preserved⟩

end DuplicatePrefix.GeneralBorrowPermissions

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowPermissions." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general borrow dependency {dependency}"
