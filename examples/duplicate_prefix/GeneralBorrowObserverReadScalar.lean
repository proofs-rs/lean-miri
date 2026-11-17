import duplicate_prefix.GeneralBorrowReadCapabilityNormal

namespace DuplicatePrefix.GeneralBorrowObserverReadScalar
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixScalarBothAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Unprotected foreign observers accept every physically possible state. -/
theorem foreign_unheld (state : LocationState) (possible : state.possible = true) :
    Both state .ForeignAccess false := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;>
      simp_all [Both,DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;>
      simp_all [Both,DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
        GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]

/-- Local source Read preserves a local observer's Both table even when the
actual and virtual protector flags differ. Source Write is never required. -/
theorem local_transition (state : LocationState) (actualHeld virtualHeld : Bool)
    (observer : Both state .LocalAccess virtualHeld)
    (source : GeneralBorrowReadCapabilityNormal.ReadCompatible state .LocalAccess actualHeld) :
    ∃ next delta,state.performAccess .Read .LocalAccess actualHeld = .Success next delta ∧
      Both next .LocalAccess virtualHeld := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases actualHeld <;> cases virtualHeld <;>
      simp [Both,GeneralBorrowReadCapabilityNormal.ReadCompatible,DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,GeneralBorrowExposedConditionalWritePermissions.Compatible,
        LocationState.possible,Permission.isUnique] at observer source <;>
      (refine ⟨_,_,rfl,?_⟩;simp [Both,DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,GeneralBorrowExposedConditionalWritePermissions.Compatible,
        LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign])
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases actualHeld <;> cases virtualHeld <;>
      simp [Both,GeneralBorrowReadCapabilityNormal.ReadCompatible,DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,GeneralBorrowExposedConditionalWritePermissions.Compatible,
        LocationState.possible,Permission.isUnique] at observer source <;>
      (refine ⟨_,_,rfl,?_⟩;simp [Both,DuplicatePrefixScalarAuthorization.Compatible,
        GeneralBorrowProtectedReadCompatible.Compatible,GeneralBorrowExposedConditionalWritePermissions.Compatible,
        LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign])

/-- Raw relation/protector geometry separates source Read authorization from
an independent mutable observer capability under virtually erased protection. -/
theorem transition (state : LocationState) (observerRelated sourceRelated : AccessRelatedness)
    (actualHeld virtualHeld : Bool)
    (observer : Both state observerRelated virtualHeld)
    (source : GeneralBorrowReadCapabilityNormal.ReadCompatible state sourceRelated actualHeld)
    (localSource : observerRelated = .LocalAccess → sourceRelated = .LocalAccess)
    (foreignLocal : observerRelated = .ForeignAccess → sourceRelated = .LocalAccess → virtualHeld = false)
    (foreignHeld : sourceRelated = .ForeignAccess → actualHeld = virtualHeld) :
    ∃ next delta,state.performAccess .Read sourceRelated actualHeld = .Success next delta ∧
      Both next observerRelated virtualHeld := by
  cases observerRelated with
  | LocalAccess =>
    have relation := localSource rfl
    subst sourceRelated
    exact local_transition state actualHeld virtualHeld observer source
  | ForeignAccess =>
    cases sourceRelated with
    | LocalAccess =>
      have erased := foreignLocal rfl rfl
      subst virtualHeld
      obtain ⟨next,delta,actual,possible⟩ := GeneralBorrowReadCapabilityNormal.transition state .LocalAccess actualHeld source
      exact ⟨next,delta,actual,foreign_unheld next possible.1⟩
    | ForeignAccess =>
      have same := foreignHeld rfl
      subst actualHeld
      exact DuplicatePrefixScalarBothAuthorization.transition state .ForeignAccess virtualHeld .Read observer

/-- The actual record/access pipeline retains the observer guarantee. Only
source Read data supplies the executed operation's permission contract. -/
theorem visit (state : LocationState) (observerRelated sourceRelated : AccessRelatedness)
    (actualHeld virtualHeld : Bool)
    (observer : Both state observerRelated virtualHeld)
    (source : GeneralBorrowReadCapabilityNormal.ReadCompatible state sourceRelated actualHeld)
    (localSource : observerRelated = .LocalAccess → sourceRelated = .LocalAccess)
    (foreignLocal : observerRelated = .ForeignAccess → sourceRelated = .LocalAccess → virtualHeld = false)
    (foreignHeld : sourceRelated = .ForeignAccess → actualHeld = virtualHeld) :
    state.skipIfKnownNoop .Read sourceRelated = .SkipSelfAndChildren ∨
      ∃ recorded next delta,state.recordNewAccess .Read sourceRelated = .Recorded recorded ∧
        recorded.performAccess .Read sourceRelated actualHeld = .Success next delta ∧ Both next observerRelated virtualHeld := by
  cases skip : state.skipIfKnownNoop .Read sourceRelated with
  | SkipSelfAndChildren => exact .inl rfl
  | Recurse =>
    let recorded := {state with idempotentForeignAccess := (IdempotentForeignAccess.recordNew state.idempotentForeignAccess
      (IdempotentForeignAccess.fromAccessAndRelatedness .Read sourceRelated))}
    have inheritedObserver : Both recorded observerRelated virtualHeld := by cases observerRelated <;> exact observer
    have inheritedSource : GeneralBorrowReadCapabilityNormal.ReadCompatible recorded sourceRelated actualHeld := by
      cases sourceRelated <;> exact source
    obtain ⟨next,delta,actual,preserved⟩ := transition recorded observerRelated sourceRelated actualHeld virtualHeld
      inheritedObserver inheritedSource localSource foreignLocal foreignHeld
    exact .inr ⟨recorded,next,delta,by simp [LocationState.recordNewAccess,skip,recorded],actual,preserved⟩

end DuplicatePrefix.GeneralBorrowObserverReadScalar
