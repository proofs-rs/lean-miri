import Miri.Memory.Identity
import Lean

namespace DuplicatePrefix.CandidateFreezeContentResources
open Miri.Memory
set_option autoImplicit false

/-! UNADOPTED semantic candidate for available Freeze CONTENT resources.
This is not ordinary validity or a reconstruction from BorrowTree. Cell wrapper
references confer no content charge here; ambient Cell grants are not excluded.
Raw scalar/protector realization is a separate, explicit specification clause.
-/
abbrev Byte := AllocId × Nat
abbrev Owner := Nat
inductive Mode where | mut | read | ret deriving DecidableEq, Repr
inductive Role where | active | suspended deriving DecidableEq, Repr
structure Charge where
  mode : Mode
  role : Role
  deriving DecidableEq, Repr
abbrev Fragment := Byte → Owner → Option Charge

/-- Suspended parent entitlements coexist with delegated rights. Only active
read content charges share a byte. This says nothing about Cell wrappers. -/
def Compatible (first second : Charge) : Prop :=
  first.role = .suspended ∨ second.role = .suspended ∨
    (first.mode = .read ∧ second.mode = .read)
def Valid (F : Fragment) : Prop :=
  ∀ byte first second firstCharge secondCharge, first ≠ second →
    F byte first = some firstCharge → F byte second = some secondCharge →
    Compatible firstCharge secondCharge

def empty : Fragment := fun _ _ => none
def union (first second : Fragment) : Fragment := fun byte owner =>
  match first byte owner with | some charge => some charge | none => second byte owner
/-- Partial composition checks distinct resource keys and cross-fragment
content compatibility; it does not mention function arguments or return slots. -/
def Composable (first second : Fragment) : Prop :=
  Valid first ∧ Valid second ∧
    (∀ byte owner, first byte owner = none ∨ second byte owner = none) ∧
    (∀ byte firstOwner secondOwner firstCharge secondCharge,
      first byte firstOwner = some firstCharge → second byte secondOwner = some secondCharge →
      Compatible firstCharge secondCharge)

private theorem origin (first second : Fragment) (byte : Byte) (owner : Owner) (charge : Charge)
    (found : union first second byte owner = some charge) :
    first byte owner = some charge ∨ second byte owner = some charge := by
  cases h : first byte owner with
  | none => exact Or.inr (by simpa only [union,h] using found)
  | some value => exact Or.inl (by simpa only [union,h] using found)
private theorem compatible_symm {first second : Charge} (h : Compatible first second) : Compatible second first := by
  rcases h with first | second | ⟨left,right⟩
  · exact Or.inr (Or.inl first)
  · exact Or.inl second
  · exact Or.inr (Or.inr ⟨right,left⟩)

theorem union_valid (first second : Fragment) (together : Composable first second) : Valid (union first second) := by
  intro byte left right leftCharge rightCharge different leftAt rightAt
  rcases origin first second byte left leftCharge leftAt with leftAt | leftAt
  all_goals rcases origin first second byte right rightCharge rightAt with rightAt | rightAt
  · exact together.1 byte left right leftCharge rightCharge different leftAt rightAt
  · exact together.2.2.2 byte left right leftCharge rightCharge leftAt rightAt
  · exact compatible_symm (together.2.2.2 byte right left rightCharge leftCharge rightAt leftAt)
  · exact together.2.1 byte left right leftCharge rightCharge different leftAt rightAt

theorem union_empty (F : Fragment) : union F empty = F ∧ union empty F = F := by
  constructor
  · funext byte owner;cases h : F byte owner <;> simp only [union,empty,h]
  · rfl
theorem union_assoc (first second third : Fragment) :
    union (union first second) third = union first (union second third) := by
  funext byte owner
  cases h : first byte owner <;> simp only [union,h]

theorem active_exclusive_conflict (F : Fragment) (valid : Valid F) (byte : Byte)
    (first second : Owner) (firstMode secondMode : Mode) (different : first ≠ second)
    (firstAt : F byte first = some ⟨firstMode,.active⟩)
    (secondAt : F byte second = some ⟨secondMode,.active⟩)
    (exclusive : firstMode ≠ .read ∨ secondMode ≠ .read) : False := by
  have permitted := valid byte first second _ _ different firstAt secondAt
  rcases permitted with impossible | impossible | ⟨left,right⟩
  · cases impossible
  · cases impossible
  · rcases exclusive with noRead | noRead
    · exact noRead left
    · exact noRead right

/-- The small fragment admits Freeze mutable/read delegation only. Return
reservations do not delegate; UnsafeCell content and pinning modes are outside
this candidate. No requirement is imposed on ambient raw Cell permissions. -/
def MayDelegate (parent child : Mode) : Prop :=
  (parent = .mut ∧ (child = .mut ∨ child = .read)) ∨ (parent = .read ∧ child = .read)
def CanDelegate (F : Fragment) (parent child : Owner) (bytes : Byte → Bool) (mode : Mode) : Prop :=
  parent ≠ child ∧ (∀ byte, F byte child = none) ∧
    ∀ byte, bytes byte = true → ∃ parentMode,
      F byte parent = some ⟨parentMode,.active⟩ ∧ MayDelegate parentMode mode
/-- Pure resource transfer: the parent keeps a suspended entitlement on the
child footprint. It supplies no interpreter transition or future-success fact. -/
def delegate (F : Fragment) (parent child : Owner) (bytes : Byte → Bool) (mode : Mode) : Fragment :=
  fun byte owner => if bytes byte then
    if owner = child then some ⟨mode,.active⟩ else if owner = parent then
      (F byte parent).map (fun charge => {charge with role := .suspended}) else F byte owner
    else F byte owner

end DuplicatePrefix.CandidateFreezeContentResources
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateFreezeContentResources." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved candidate content resource dependency {dependency}"
