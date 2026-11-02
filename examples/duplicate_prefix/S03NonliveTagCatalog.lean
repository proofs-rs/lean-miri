import duplicate_prefix.GenericFunctionEntryNumerics

namespace DuplicatePrefix.S03NonliveTagCatalog
open Miri.Memory
set_option autoImplicit false

def shift (i : Fin 6) : Nat := if i.val = 0 then 6 else if i.val = 1 then 0 else i.val

theorem shift_le (i : Fin 6) : shift i ≤ 6 := by
  simp only [shift]
  split <;> first | omega | (split <;> omega)

def catalog (tag : BorTag) (room : tag.value.toNat+16 < 2^64) (i : Fin 6) : BorTag :=
  ⟨UInt64.ofNat (tag.value.toNat+shift i),by
    intro zero
    have fits : tag.value.toNat+shift i < 2^64 := by have := shift_le i;omega
    have equal := congrArg UInt64.toNat zero
    rw [UInt64.toNat_ofNat_of_lt' fits] at equal
    have positive : 0 < tag.value.toNat := by
      have ne : tag.value.toNat ≠ 0 := by intro same;apply tag.nonzero;exact UInt64.toNat_inj.mp same
      omega
    simp only [UInt64.toNat_zero] at equal
    omega⟩

theorem value (tag : BorTag) (room : tag.value.toNat+16 < 2^64) (i : Fin 6) :
    (catalog tag room i).value.toNat = tag.value.toNat+shift i := by
  exact UInt64.toNat_ofNat_of_lt' (show tag.value.toNat+shift i < 18446744073709551616 by have := shift_le i;omega)

theorem injective (tag : BorTag) (room : tag.value.toNat+16 < 2^64) :
    Function.Injective (catalog tag room) := by
  intro i j equal
  have eq := congrArg (fun t : BorTag => t.value.toNat) equal
  rw [value,value] at eq
  apply Fin.ext
  have ib := i.isLt
  have jb := j.isLt
  by_cases i0 : i.val = 0 <;> by_cases i1 : i.val = 1 <;>
    by_cases j0 : j.val = 0 <;> by_cases j1 : j.val = 1 <;>
    simp [shift,i0,i1,j0,j1] at eq <;> omega

/-- Finite names needed by the existing component interfaces are generated
from the initial sixteen-tag budget; they impose no additional caller field. -/
theorem first (tag : BorTag) (room : tag.value.toNat+16 < 2^64) : catalog tag room 1 = tag := by
  cases tag with
  | mk val nonzero => simp [catalog,shift]

end DuplicatePrefix.S03NonliveTagCatalog
