import Lean
import Miri.TreeBorrows.LocationState

namespace DuplicatePrefix.S05ForeignWriteNoopClassification
open Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false

/-- Exact classification of unprotected foreign Write transitions that return
normally with the entire location state unchanged. Accessed and SIFA are
arbitrary; no possible-state or operation-success premise is required.
This classifies performAccess only, not the separate SIFA recording operation. -/
theorem foreign_write_same_state_iff (state : LocationState) :
    (∃ delta, state.performAccess .Write .ForeignAccess false = .Success state delta) ↔
      state.permission = .Disabled ∨ state.permission = .Cell ∨
        state.permission = .ReservedIM := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | Disabled =>
      constructor
      · intro _; exact Or.inl rfl
      · intro _; exact ⟨⟨.Disabled,.Disabled⟩,by cases accessed <;> rfl⟩
  | Cell =>
      constructor
      · intro _; exact Or.inr (Or.inl rfl)
      · intro _; exact ⟨⟨.Cell,.Cell⟩,by cases accessed <;> rfl⟩
  | ReservedIM =>
      constructor
      · intro _; exact Or.inr (Or.inr rfl)
      · intro _; exact ⟨⟨.ReservedIM,.ReservedIM⟩,by cases accessed <;> rfl⟩
  | ReservedFrz conflicted =>
      constructor
      · rintro ⟨delta,h⟩
        cases conflicted <;> cases accessed <;> cases h
      · intro h
        rcases h with h | h | h <;> cases h
  | Unique =>
      constructor
      · rintro ⟨delta,h⟩
        cases accessed <;> cases h
      · intro h
        rcases h with h | h | h <;> cases h
  | Frozen =>
      constructor
      · rintro ⟨delta,h⟩
        cases accessed <;> cases h
      · intro h
        rcases h with h | h | h <;> cases h

/-- ReservedIM foreign Read and Write preserve every location-state field
when unprotected. This does not justify suppressing a required SIFA record. -/
theorem reserved_im_foreign_unprotected (accessed : Bool)
    (sifa : IdempotentForeignAccess) (kind : AccessKind) :
    (⟨.ReservedIM,accessed,sifa⟩ : LocationState).performAccess kind .ForeignAccess false =
      .Success ⟨.ReservedIM,accessed,sifa⟩ ⟨.ReservedIM,.ReservedIM⟩ := by
  cases kind <;> cases accessed <;> rfl

/-- The complete same-state normal-return class for a foreign Write, including
protected states. No reachable-state, possible-state or success premise is used. -/
theorem foreign_write_same_state_iff_held (state : LocationState) (held : Bool) :
    (∃ delta, state.performAccess .Write .ForeignAccess held = .Success state delta) ↔
      state.permission = .Cell ∨
        (state.permission = .Disabled ∧ (held = false ∨ state.accessed = false)) ∨
        (state.permission = .ReservedIM ∧ held = false) := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | Cell =>
      constructor
      · intro _; simp
      · intro _; exact ⟨⟨.Cell,.Cell⟩,by cases held <;> cases accessed <;> rfl⟩
  | Disabled =>
      cases held with
      | false =>
          constructor
          · intro _; simp
          · intro _; exact ⟨⟨.Disabled,.Disabled⟩,by cases accessed <;> rfl⟩
      | true =>
          cases accessed with
          | false =>
              constructor
              · intro _; simp
              · intro _; exact ⟨⟨.Disabled,.Disabled⟩,rfl⟩
          | true =>
              constructor
              · rintro ⟨delta,h⟩; cases h
              · intro h; simp at h
  | ReservedIM =>
      cases held with
      | false =>
          constructor
          · intro _; simp
          · intro _; exact ⟨⟨.ReservedIM,.ReservedIM⟩,by cases accessed <;> rfl⟩
      | true =>
          constructor
          · rintro ⟨delta,h⟩; cases h
          · intro h; simp at h
  | ReservedFrz conflicted =>
      constructor
      · rintro ⟨delta,h⟩
        cases conflicted <;> cases held <;> cases accessed <;> cases h
      · intro h; simp at h
  | Unique =>
      constructor
      · rintro ⟨delta,h⟩
        cases held <;> cases accessed <;> cases h
      · intro h; simp at h
  | Frozen =>
      constructor
      · rintro ⟨delta,h⟩
        cases held <;> cases accessed <;> cases h
      · intro h; simp at h

/-- Every member of the Write no-op class also normally preserves the whole
state under a foreign Read. This is a sufficient class for Read, not an
exhaustive classification of Read no-ops, and concerns performAccess alone. -/
theorem write_noop_class_foreign_all_kinds (state : LocationState) (held : Bool)
    (eligible : state.permission = .Cell ∨
      (state.permission = .Disabled ∧ (held = false ∨ state.accessed = false)) ∨
      (state.permission = .ReservedIM ∧ held = false)) (kind : AccessKind) :
    state.performAccess kind .ForeignAccess held =
      .Success state ⟨state.permission,state.permission⟩ := by
  rcases state with ⟨permission,accessed,sifa⟩
  rcases eligible with hp | ⟨hp,h⟩ | ⟨hp,h⟩
  · cases hp
    cases kind <;> cases held <;> cases accessed <;> rfl
  · cases hp
    rcases h with h | h
    · cases h
      cases kind <;> cases accessed <;> rfl
    · cases h
      cases kind <;> cases held <;> rfl
  · cases hp
    cases h
    exact reserved_im_foreign_unprotected accessed sifa kind

/-- A protected accessed Disabled state retains the exact source error for
both foreign access kinds, including every field of the returned state. -/
theorem protected_accessed_disabled_foreign_error
    (sifa : IdempotentForeignAccess) (kind : AccessKind) :
    (⟨.Disabled,true,sifa⟩ : LocationState).performAccess kind .ForeignAccess true =
      .Error ⟨.Disabled,true,sifa⟩ (.ProtectedDisabled .Disabled) := by
  cases kind <;> rfl

/-- Protected ReservedIM remains a permission invariant failure, for either
foreign access kind and either accessed bit. -/
theorem protected_reserved_im_foreign_error (accessed : Bool)
    (sifa : IdempotentForeignAccess) (kind : AccessKind) :
    (⟨.ReservedIM,accessed,sifa⟩ : LocationState).performAccess kind .ForeignAccess true =
      .PermissionInvariantFailure ⟨.ReservedIM,accessed,sifa⟩ := by
  cases kind <;> rfl

end DuplicatePrefix.S05ForeignWriteNoopClassification
