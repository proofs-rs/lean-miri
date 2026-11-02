import duplicate_prefix.GeneralBorrowExposedNonleafCoherentAccess
namespace DuplicatePrefix.GeneralBorrowExposedConditionalReadPermissions
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedReadCompatible (Compatible)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def Condition (zero : Bool) (state : LocationState) (held : Bool) : Prop :=
  Compatible state (if zero then .ForeignAccess else .LocalAccess) held

theorem transition (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : Compatible state related held) :
    ∃ next delta, state.performAccess .Read related held = .Success next delta ∧
      Compatible next related held ∧
      GeneralBorrowExposureCardinality.supports (next.permission.strongestAllowedLocalAccess held) .Read =
        GeneralBorrowExposureCardinality.supports (state.permission.strongestAllowedLocalAccess held) .Read := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Compatible,LocationState.possible,Permission.isUnique] at initial <;>
      (refine ⟨_,_,rfl,?_,?_⟩; all_goals simp [Compatible,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign,
        GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsRead])
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Compatible,LocationState.possible,Permission.isUnique] at initial <;>
      (refine ⟨_,_,rfl,?_,?_⟩; all_goals simp [Compatible,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign,
        GeneralBorrowExposureCardinality.supports,Permission.strongestAllowedLocalAccess,GeneralBorrowExposureAncestorFold.supportsRead])

theorem visit (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : Compatible state related held) (scheduled : GeneralBorrowEvents.Scheduled state .Read related) :
    ∃ recorded next delta, state.recordNewAccess .Read related = .Recorded recorded ∧
      recorded.performAccess .Read related held = .Success next delta ∧ Compatible next related held ∧
      GeneralBorrowExposureCardinality.supports (next.permission.strongestAllowedLocalAccess held) .Read =
        GeneralBorrowExposureCardinality.supports (state.permission.strongestAllowedLocalAccess held) .Read := by
  let recorded := {state with idempotentForeignAccess := (IdempotentForeignAccess.recordNew state.idempotentForeignAccess
    (IdempotentForeignAccess.fromAccessAndRelatedness .Read related))}
  have good : Compatible recorded related held := initial
  obtain ⟨next,delta,actual,compatible,support⟩ := transition recorded related held good
  refine ⟨recorded,next,delta,?_,actual,compatible,support⟩
  simp only [LocationState.recordNewAccess,GeneralBorrowEvents.scheduled_recurse state .Read related scheduled,beq_self_eq_true,↓reduceIte]
  rfl

theorem local_allows (state : LocationState) (held : Bool) (good : Compatible state .LocalAccess held) :
    (state.permission.strongestAllowedLocalAccess held).allows .Read = true := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted => cases conflicted <;> cases held <;> simp_all [Compatible,Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]
  | Cell | ReservedIM | Unique | Frozen | Disabled => cases held <;> simp_all [Compatible,Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]
end DuplicatePrefix.GeneralBorrowExposedConditionalReadPermissions
