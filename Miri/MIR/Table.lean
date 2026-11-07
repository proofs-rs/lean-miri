namespace Miri.MIR

abbrev SharedTable (α : Type) := Array (Option α)

namespace SharedTable

def lookup (table : SharedTable α) (id : Nat) : Except Nat α :=
  match table[id]? with
  | some (some value) => .ok value
  | _ => .error id

theorem lookup_some (table : SharedTable α) (id : Nat) (value : α)
    (h : table[id]? = some (some value)) : lookup table id = .ok value := by
  simp [lookup, h]

end SharedTable
end Miri.MIR
