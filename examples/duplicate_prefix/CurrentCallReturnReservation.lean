import duplicate_prefix.CandidateFreezeContentResources

/-! Scoped exclusive output reservations. This is not content delegation: the
original active charge is suspended while the temporary reservation owns the
footprint actively. The original destination remains in the scope record.
No initialized value, raw access success, or MayDelegate fact is required. -/
namespace DuplicatePrefix.CurrentCallReturnReservation
open CandidateFreezeContentResources
set_option autoImplicit false

/-- Exchange resource names without manufacturing a second exclusive charge. -/
def exchange (original temporary owner : Owner) : Owner :=
  if owner = original then temporary else if owner = temporary then original else owner

theorem exchange_involution (original temporary owner : Owner) :
    exchange original temporary (exchange original temporary owner) = owner := by
  by_cases same : original = temporary
  · subst temporary
    by_cases equal : owner = original <;> simp [exchange,equal]
  · by_cases first : owner = original
    · subst owner; simp [exchange,Ne.symm same]
    · by_cases second : owner = temporary
      · subst owner; simp [exchange,Ne.symm same]
      · simp [exchange,first,second]

/-- Only bytes in the actual destination window change owner. -/
def reserve (F : Fragment) (original temporary : Owner) (window : Byte → Prop)
    [DecidablePred window] : Fragment :=
  fun byte owner => if window byte then F byte (exchange original temporary owner) else F byte owner

theorem reserve_valid (F : Fragment) (valid : Valid F) (original temporary : Owner)
    (window : Byte → Prop) [DecidablePred window] : Valid (reserve F original temporary window) := by
  intro byte first second firstCharge secondCharge different firstAt secondAt
  by_cases inside : window byte
  · simp only [reserve,ite_eq_left inside] at firstAt secondAt
    apply valid byte _ _ firstCharge secondCharge _ firstAt secondAt
    intro equal
    have := congrArg (exchange original temporary) equal
    exact different (by simpa only [exchange_involution] using this)
  · simp only [reserve,ite_eq_right inside] at firstAt secondAt
    exact valid byte first second firstCharge secondCharge different firstAt secondAt

theorem reserve_twice (F : Fragment) (original temporary : Owner)
    (window : Byte → Prop) [DecidablePred window] :
    reserve (reserve F original temporary window) original temporary window = F := by
  funext byte owner
  by_cases inside : window byte <;> simp [reserve,inside,exchange_involution]

/-- The fresh reservation owns the output footprint; the caller's old owner
has no content charge there. Freshness is explicit even for suspended owners. -/
theorem reserved_charge (F : Fragment) (original temporary : Owner)
    (different : original ≠ temporary) (window : Byte → Prop) [DecidablePred window]
    (fresh : ∀ byte, F byte temporary = none)
    (owned : ∀ byte, window byte → F byte original = some ⟨.ret,.active⟩)
    (byte : Byte) (inside : window byte) :
    reserve F original temporary window byte temporary = some ⟨.ret,.active⟩ ∧
    reserve F original temporary window byte original = none := by
  simp [reserve,inside,exchange,Ne.symm different,fresh,owned byte inside]

/-- Resource bookkeeping returns exactly to its initial fragment under the
inverse exchange. This theorem does not establish interpreter authority at the
original grant: that requires the actual release/endCall transition. -/
theorem restored_valid (F : Fragment) (valid : Valid F) (original temporary : Owner)
    (window : Byte → Prop) [DecidablePred window] :
    Valid (reserve (reserve F original temporary window) original temporary window) := by
  rw [reserve_twice]
  exact valid

/-- The original reservation is visibly suspended while the fresh name holds
its active output charge. This is one scoped reservation, not MayDelegate. -/
def begin (F : Fragment) (original temporary : Owner) (window : Byte → Prop)
    [DecidablePred window] : Fragment := fun byte owner =>
  if window byte ∧ owner = original then some ⟨.ret,.suspended⟩
  else reserve F original temporary window byte owner

theorem begin_valid (F : Fragment) (valid : Valid F) (original temporary : Owner)
    (window : Byte → Prop) [DecidablePred window] : Valid (begin F original temporary window) := by
  intro byte first second firstCharge secondCharge different firstAt secondAt
  by_cases firstSuspended : window byte ∧ first = original
  · simp only [begin,ite_eq_left firstSuspended] at firstAt
    cases Option.some.inj firstAt
    exact Or.inl rfl
  · by_cases secondSuspended : window byte ∧ second = original
    · simp only [begin,ite_eq_left secondSuspended] at secondAt
      cases Option.some.inj secondAt
      exact Or.inr (Or.inl rfl)
    · simp only [begin,ite_eq_right firstSuspended] at firstAt
      simp only [begin,ite_eq_right secondSuspended] at secondAt
      exact reserve_valid F valid original temporary window byte first second firstCharge secondCharge different firstAt secondAt

theorem begin_charges (F : Fragment) (original temporary : Owner)
    (different : original ≠ temporary) (window : Byte → Prop) [DecidablePred window]
    (owned : ∀ byte, window byte → F byte original = some ⟨.ret,.active⟩)
    (byte : Byte) (inside : window byte) :
    begin F original temporary window byte original = some ⟨.ret,.suspended⟩ ∧
    begin F original temporary window byte temporary = some ⟨.ret,.active⟩ := by
  simp [begin,reserve,exchange,inside,Ne.symm different,owned byte inside]

theorem begin_outside (F : Fragment) (original temporary : Owner)
    (window : Byte → Prop) [DecidablePred window] (byte : Byte) (outside : ¬ window byte)
    (owner : Owner) : begin F original temporary window byte owner = F byte owner := by
  simp [begin,reserve,outside]

theorem begin_other (F : Fragment) (original temporary : Owner)
    (window : Byte → Prop) [DecidablePred window] (byte : Byte) (owner : Owner)
    (notOriginal : owner ≠ original) (notTemporary : owner ≠ temporary) :
    begin F original temporary window byte owner = F byte owner := by
  by_cases inside : window byte <;> simp [begin,reserve,exchange,inside,notOriginal,notTemporary]

/-- Bookkeeping inverse, to be used alongside actual release and whole-frame
endCall evidence; it alone supplies no raw original-grant authority. -/
def finish (F : Fragment) (original temporary : Owner) (window : Byte → Prop)
    [DecidablePred window] : Fragment := fun byte owner =>
  if window byte then
    if owner = original then some ⟨.ret,.active⟩ else
    if owner = temporary then none else F byte owner
  else F byte owner

theorem finish_begin (F : Fragment) (original temporary : Owner)
    (different : original ≠ temporary) (window : Byte → Prop) [DecidablePred window]
    (fresh : ∀ byte, F byte temporary = none)
    (owned : ∀ byte, window byte → F byte original = some ⟨.ret,.active⟩) :
    finish (begin F original temporary window) original temporary window = F := by
  funext byte owner
  by_cases inside : window byte
  · by_cases first : owner = original
    · subst owner; simp [finish,inside,owned byte inside]
    · by_cases second : owner = temporary
      · subst owner; simp [finish,inside,Ne.symm different,fresh]
      · simp [finish,begin,reserve,exchange,inside,first,second]
  · simp [finish,begin,reserve,inside]

/-- Original destination identity is independent of the temporary resource name.
The scope stores no Bool value or initialization assumption. -/
structure Scope (Destination : Type) where
  originalDestination : Destination
  originalOwner : Owner
  temporaryOwner : Owner
  distinct : originalOwner ≠ temporaryOwner
  window : Byte → Prop
  before : Fragment
  fresh : ∀ byte, before byte temporaryOwner = none
  owned : ∀ byte, window byte → before byte originalOwner = some ⟨.ret,.active⟩

theorem scope_restoration {Destination : Type} (scope : Scope Destination)
    [DecidablePred scope.window] :
    finish (begin scope.before scope.originalOwner scope.temporaryOwner scope.window)
      scope.originalOwner scope.temporaryOwner scope.window = scope.before :=
  finish_begin scope.before scope.originalOwner scope.temporaryOwner scope.distinct scope.window scope.fresh scope.owned

end DuplicatePrefix.CurrentCallReturnReservation
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallReturnReservation." then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved return reservation dependency {dependency}"
