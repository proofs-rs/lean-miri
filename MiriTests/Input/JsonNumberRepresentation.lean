import Lean
open Lean

def main : IO Unit := do
  let valid := Json.num ⟨1, 0⟩
  let cache : Std.HashMap Json Nat := ({} : Std.HashMap Json Nat).insert valid 99
  IO.println s!"valid={reprStr valid.getNat?}"
  for exponent in [:1000] do
    let candidate := Json.num ⟨Int.ofNat (10^exponent), exponent⟩
    if candidate == valid then
      if let some result := cache[candidate]? then
        IO.println s!"hit_exponent={exponent};candidate_nat={reprStr candidate.getNat?};cached={result};raw_hash_equal={hash candidate == hash valid}"
