import duplicate_prefix.CurrentCallReturnReservation
import duplicate_prefix.CurrentCallOwnerRenaming

/-! Fresh reservation names are constructed by shifting EVERY old owner,
including arbitrarily many suspended owners. No caller freshness gate. -/
namespace DuplicatePrefix.CurrentCallReturnReservationShift
open CandidateFreezeContentResources CurrentCallReturnReservation CurrentCallOwnerRenaming
set_option autoImplicit false

/-- Retain the original destination while reserving owner zero internally. -/
def scope {Destination : Type} (destination : Destination) (F : Fragment)
    (original : Owner) (window : Byte → Prop)
    (owned : ∀ byte, window byte → F byte original = some ⟨.ret,.active⟩) :
    Scope Destination where
  originalDestination := destination
  originalOwner := original + 1
  temporaryOwner := 0
  distinct := Nat.succ_ne_zero original
  window := window
  before := shiftContent F
  fresh := shiftContent_zero F
  owned := by intro byte inside; exact owned byte inside

theorem original_destination {Destination : Type} (destination : Destination) (F : Fragment)
    (original : Owner) (window : Byte → Prop)
    (owned : ∀ byte, window byte → F byte original = some ⟨.ret,.active⟩) :
    (scope destination F original window owned).originalDestination = destination := rfl

theorem begin_valid_shifted (F : Fragment) (valid : Valid F) (original : Owner)
    (window : Byte → Prop) [DecidablePred window] :
    Valid (begin (shiftContent F) (original + 1) 0 window) :=
  begin_valid _ (shiftContent_valid valid) _ _ _

theorem shifted_charges (F : Fragment) (original : Owner)
    (window : Byte → Prop) [DecidablePred window]
    (owned : ∀ byte, window byte → F byte original = some ⟨.ret,.active⟩)
    (byte : Byte) (inside : window byte) :
    begin (shiftContent F) (original + 1) 0 window byte (original + 1) = some ⟨.ret,.suspended⟩ ∧
    begin (shiftContent F) (original + 1) 0 window byte 0 = some ⟨.ret,.active⟩ :=
  begin_charges _ _ _ (Nat.succ_ne_zero original) window (by intro b h; exact owned b h) byte inside

theorem exact_restore (F : Fragment) (original : Owner)
    (window : Byte → Prop) [DecidablePred window]
    (owned : ∀ byte, window byte → F byte original = some ⟨.ret,.active⟩) :
    finish (begin (shiftContent F) (original + 1) 0 window) (original + 1) 0 window = shiftContent F :=
  finish_begin _ _ _ (Nat.succ_ne_zero original) window (shiftContent_zero F) (by intro b h; exact owned b h)

/-- All other owners, whether active or suspended and without finite support,
retain their exact old charges on every byte. -/
theorem other_preserved (F : Fragment) (original other : Owner) (different : other ≠ original)
    (window : Byte → Prop) [DecidablePred window] (byte : Byte) :
    begin (shiftContent F) (original + 1) 0 window byte (other + 1) = F byte other := by
  rw [begin_other _ _ _ _ _ _ (fun equal => different (Nat.succ.inj equal)) (Nat.succ_ne_zero other)]
  rfl

/-- Resource compatibility supplies footprint disjointness even when source
and destination occupy the SAME allocation. -/
theorem source_return_disjoint (F : Fragment) (valid : Valid F) (source original : Owner)
    (different : source ≠ original) (sourceWindow returnWindow : Byte → Prop)
    (sourceOwned : ∀ byte, sourceWindow byte → F byte source = some ⟨.mut,.active⟩)
    (returnOwned : ∀ byte, returnWindow byte → F byte original = some ⟨.ret,.active⟩) :
    ∀ byte, sourceWindow byte → ¬ returnWindow byte := by
  intro byte sourceAt returnAt
  exact active_exclusive_conflict F valid byte source original .mut .ret different
    (sourceOwned byte sourceAt) (returnOwned byte returnAt) (Or.inl (by decide))

end DuplicatePrefix.CurrentCallReturnReservationShift
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallReturnReservationShift." then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shifted reservation dependency {dependency}"
