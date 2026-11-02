import duplicate_prefix.GeneralBorrowExposedConditionalReadAccess
namespace DuplicatePrefix.GeneralBorrowExposedConditionalWritePermissions
open Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Raw scalar permission/protector/accessed conditions for an exact Write.
Held inactive rows may be disabled by a foreign Write; held active Cell rows
are retained. Local conflicted held reservations remain forbidden. -/
def Compatible (state : LocationState) (related : AccessRelatedness) (held : Bool) : Prop :=
  state.possible = true ∧ match related with
  | .LocalAccess => state.permission ≠ .Disabled ∧ state.permission ≠ .Frozen ∧
      (held = true → state.permission ≠ .ReservedFrz true)
  | .ForeignAccess => held = true → state.permission = .Cell ∨
      (state.permission ≠ .ReservedIM ∧ state.accessed = false)

def Condition (zero : Bool) (state : LocationState) (held : Bool) : Prop :=
  Compatible state (if zero then .ForeignAccess else .LocalAccess) held

def support (state : LocationState) (held : Bool) : Bool :=
  GeneralBorrowExposureCardinality.supports (state.permission.strongestAllowedLocalAccess held) .Write

theorem transition (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : Compatible state related held) :
    ∃ next delta, state.performAccess .Write related held = .Success next delta ∧
      Compatible next related held ∧
      (related = .LocalAccess → support next held = support state held) ∧
      (support state held = false → support next held = false) := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Compatible,LocationState.possible,Permission.isUnique] at initial <;>
      (refine ⟨_,_,rfl,?_,?_,?_⟩; all_goals simp [Compatible,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign,
        support,GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsWrite])
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Compatible,LocationState.possible,Permission.isUnique] at initial <;>
      (refine ⟨_,_,rfl,?_,?_,?_⟩; all_goals simp [Compatible,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign,
        support,GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsWrite])

theorem visit (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : Compatible state related held) (scheduled : GeneralBorrowEvents.Scheduled state .Write related) :
    ∃ recorded next delta, state.recordNewAccess .Write related = .Recorded recorded ∧
      recorded.performAccess .Write related held = .Success next delta ∧ Compatible next related held ∧
      (related = .LocalAccess → support next held = support state held) ∧
      (support state held = false → support next held = false) := by
  let recorded := {state with idempotentForeignAccess := (IdempotentForeignAccess.recordNew state.idempotentForeignAccess
    (IdempotentForeignAccess.fromAccessAndRelatedness .Write related))}
  have good : Compatible recorded related held := initial
  obtain ⟨next,delta,actual,compatible,localSupport,noSupport⟩ := transition recorded related held good
  refine ⟨recorded,next,delta,?_,actual,compatible,localSupport,noSupport⟩
  simp only [LocationState.recordNewAccess,GeneralBorrowEvents.scheduled_recurse state .Write related scheduled,beq_self_eq_true,↓reduceIte]
  rfl

theorem local_allows (state : LocationState) (held : Bool) (good : Compatible state .LocalAccess held) :
    (state.permission.strongestAllowedLocalAccess held).allows .Write = true := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases held <;> simp_all [Compatible,Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases held <;> simp_all [Compatible,Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]
end DuplicatePrefix.GeneralBorrowExposedConditionalWritePermissions
