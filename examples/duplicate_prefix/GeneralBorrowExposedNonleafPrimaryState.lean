import duplicate_prefix.GeneralBorrowExposedNonleafState
namespace DuplicatePrefix.GeneralBorrowExposedNonleafPrimaryState
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafState
open GeneralBorrowWildcardRelatednessBounds (count)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def related (initial : LocationTree) (root index : UniIndex) : WildcardAccessRelatedness :=
  if count initial.exposedCache root .Read == count initial.exposedCache index .Read then .LocalAccess
  else if count initial.exposedCache index .Read == 0 then .ForeignAccess else .EitherAccess

theorem classify (initial current : LocationTree) (root index : UniIndex)
    (frame : ReadFrame initial current) (positive : 0 < count initial.exposedCache root .Read) :
    current.exposedCache.accessRelatedness root index .Read false false = some (related initial root index) := by
  have counts : ∀ query, count current.exposedCache query .Read = count initial.exposedCache query .Read :=
    fun query => congrArg UInt16.toNat (frame query)
  have rootPositive : count current.exposedCache root .Read ≠ 0 := by rw [counts];omega
  simp only [ExposedCache.accessRelatedness,Id.run,pure,Bool.false_eq_true,ite_false,Nat.add_zero]
  change (if count current.exposedCache root .Read == 0 then none else
    if count current.exposedCache root .Read == count current.exposedCache index .Read then some WildcardAccessRelatedness.LocalAccess else
    if count current.exposedCache index .Read == 0 then some WildcardAccessRelatedness.ForeignAccess else some WildcardAccessRelatedness.EitherAccess) = _
  simp only [counts,show (count initial.exposedCache root .Read == 0) = false by simp [Nat.ne_of_gt positive],Bool.false_eq_true,ite_false,related]
  split <;> first | rfl | (split <;> rfl)

theorem readable_allows (state : LocationState) (held : Bool)
    (good : GeneralBorrowProtectedReadInvariant.Readable state held) :
    (state.permission.strongestAllowedLocalAccess held).allows .Read = true := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases held <;> simp_all [GeneralBorrowProtectedReadInvariant.Readable,LocationState.possible,Permission.isUnique,
      Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases held <;> simp_all [GeneralBorrowProtectedReadInvariant.Readable,LocationState.possible,Permission.isUnique,
      Permission.strongestAllowedLocalAccess,WildcardAccessLevel.allows]

theorem positive_not_foreign (initial : LocationTree) (root index : UniIndex)
    (positive : 0 < count initial.exposedCache index .Read) :
    related initial root index ≠ .ForeignAccess := by
  unfold related
  split
  · decide
  · simp only [show (count initial.exposedCache index .Read == 0) = false by simp [Nat.ne_of_gt positive],Bool.false_eq_true,ite_false]
    decide
theorem foreign_zero (initial : LocationTree) (root index : UniIndex)
    (foreign : related initial root index = .ForeignAccess) : count initial.exposedCache index .Read = 0 := by
  unfold related at foreign
  split at foreign
  · cases foreign
  · split at foreign
    · simpa only [beq_iff_eq] using ‹(count initial.exposedCache index .Read == 0) = true›
    · cases foreign

end DuplicatePrefix.GeneralBorrowExposedNonleafPrimaryState
