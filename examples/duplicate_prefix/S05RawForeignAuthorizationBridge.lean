import duplicate_prefix.OrdinaryBorrowAuthorityBridge
import duplicate_prefix.DuplicatePrefixCallbackVisitAuthorizationRepaired
import duplicate_prefix.GeneralBorrowSifaPermissionConsistency

/-! Pointwise Foreign Write coverage. Permission/protector authority and scalar
SIFA consistency suffice for every entry classification. These are current-state
data clauses, with no removal-set, callback-success or future Result premise.
This does not establish that every conservative removal query has such authority. -/
namespace DuplicatePrefix.S05RawForeignAuthorizationBridge
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSifaPermissionConsistency OrdinaryBorrowAuthority
open DuplicatePrefixCallbackAuthorization
set_option autoImplicit false

/-- Consistency rules out a cached Write skip on permissions weaker than the
actual Write no-op class. Foreign authority supplies the held Disabled clause. -/
private theorem write_skip_noop (state : LocationState) (held : Bool)
    (consistent : Consistent state held) (authority : ForeignWrite state held)
    (skipped : state.skipIfKnownNoop .Write .ForeignAccess = .SkipSelfAndChildren) :
    state.foreignWriteNoop held = true := by
  rcases state with ⟨permission,accessed,sifa⟩
  obtain ⟨strongest,formed,bound⟩ := consistent
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases held <;> cases strongest <;>
      simp_all [ForeignWrite,LocationState.foreignWriteNoop,LocationState.skipIfKnownNoop,
        Permission.strongestIdempotentForeignAccess,Permission.isDisabled,Permission.isFrozen,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.canSkipForeignAccess,
        IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,IdempotentForeignAccess.rank,
        AccessRelatedness.isForeign]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases held <;> cases strongest <;>
      simp_all [ForeignWrite,LocationState.foreignWriteNoop,LocationState.skipIfKnownNoop,
        Permission.strongestIdempotentForeignAccess,Permission.isDisabled,Permission.isFrozen,
        IdempotentForeignAccess.fromForeign,IdempotentForeignAccess.canSkipForeignAccess,
        IdempotentForeignAccess.isLocal,IdempotentForeignAccess.le,IdempotentForeignAccess.rank,
        AccessRelatedness.isForeign]

/-- The independent raw Foreign Write clause covers the repaired callback at
ANY entry classification. A current postchildren skip uses the exact core
no-op class; otherwise the old record/transition authorization is retained. -/
theorem foreign_write_authorized (state : LocationState) (held : Bool)
    (entry : Option WildcardAccessRelatedness)
    (consistent : Consistent state held) (authority : ForeignWrite state held) :
    DuplicatePrefixCallbackVisitAuthorizationRepaired.Authorized state .Write held
      entry (some .ForeignAccess) := by
  by_cases skipped : skip state .Write .ForeignAccess = true
  · have sourceSkip := (skip_source state .Write .ForeignAccess).mp skipped
    exact .inr ⟨authority.1,rfl,write_skip_noop state held consistent authority sourceSkip,sourceSkip⟩
  · apply DuplicatePrefixCallbackVisitAuthorizationRepaired.old_inclusion
    refine ⟨authority.1,Or.inr ⟨?_,?_⟩⟩
    · exact Bool.eq_false_iff.mpr skipped
    · exact authority

end DuplicatePrefix.S05RawForeignAuthorizationBridge
