import duplicate_prefix.TypedRetagPolicyFields

/-! Shared non-Freeze policy selection in the fixed interpreter. These lemmas
consume compiler query facts; they do not manufacture a reference type in the
fixed input or certify ordinary formation of a borrow tree. -/
namespace DuplicatePrefix.TypedRetagSharedNonFreezePolicy
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Interpreter
set_option autoImplicit false

/-- A non-FnEntry shared non-Freeze retag creates an unprotected Cell grant,
independently of pinning. No current-frame or implicit-write query is needed. -/
def policy : RetagPolicy.NewPermission := ⟨.Frozen, .Cell, .Cell, none⟩

def location : Tree.LocationState := ⟨.Cell, false, .Write⟩

theorem new_permission_shared_nonfreeze {K U : Type}
    (h : TypedRetag.Hooks K U) (pointee : TyId) (unpinValue unsafeUnpinValue : Bool)
    (unpin : h.isUnpin pointee = pure unpinValue)
    (unsafeUnpin : h.isUnsafeUnpin pointee = pure unsafeUnpinValue)
    (nonfreeze : h.typeIsFreeze pointee = pure false) :
    TypedRetag.newPermission h pointee .Shared .Default = pure (some policy) := by
  funext state
  cases unpinValue <;> cases unsafeUnpinValue <;>
    simp [TypedRetag.newPermission, unpin, unsafeUnpin, nonfreeze,
      RetagPolicy.create, policy, bind, EStateM.bind, pure, EStateM.pure] <;> rfl

/-- The nonprecise policy uses the pointee Freeze query, including at size zero.
Cell starts unaccessed; its associated-access field is absent. -/
theorem inside_permissions {K U : Type} (h : TypedRetag.Hooks K U)
    (budget : Nat) (place : MPlaceTy Provenance) (size : Size)
    (precise : h.preciseInteriorMut = pure false)
    (nonfreeze : h.typeIsFreeze place.layout.ty = pure false) :
    typed_inside h budget place size policy = pure (DedupRangeMap.new size location) := by
  unfold_typed ".TypedRetag.insidePermissions"
  unfold_typed ".TypedRetag.checked"
  funext state
  simp [precise, nonfreeze, policy, location, RetagPolicy.shared_cell_starts_unaccessed,
    bind, EStateM.bind, pure, EStateM.pure]

theorem no_associated_access : location.permission.associatedAccess = none := rfl

theorem outside_cell : policy.outsidePermission = .Cell := rfl

theorem unprotected : policy.protector = none := rfl

end DuplicatePrefix.TypedRetagSharedNonFreezePolicy

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.TypedRetagSharedNonFreezePolicy." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved shared non-Freeze policy dependency {dependency}"
