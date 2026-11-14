import Miri.ABI.Layout

/-! Pinned rustc_abi::Niche::{available,reserve}, including its explicit bool
exception when selecting a zero-adjacent one-variant niche. -/
namespace Miri.ABI.NicheLayout

def available (target : RuntimeTargetDataLayout) (niche : Niche) : Except String U128 := do
  let size ← (niche.value.size target).mapError toString
  let max ← size.unsignedIntMax |>.mapError reprStr
  pure ((niche.validRange.start - niche.validRange.end - 1) &&& max)

def reserve (target : RuntimeTargetDataLayout) (niche : Niche) (count : U128) :
    Except String (Option (U128 × Scalar)) := do
  unless count.toNat > 0 do throw "niche reservation requires a positive count"
  let size ← (niche.value.size target).mapError toString
  let max ← size.unsignedIntMax |>.mapError reprStr
  if count.toNat > (← available target niche).toNat then return none
  let v := niche.validRange
  let moveStart : Option (U128 × Scalar) :=
    let start := (v.start - count) &&& max
    some (start,.Initialized (value := niche.value) (validRange := v.withStart start))
  let moveEnd : Option (U128 × Scalar) :=
    let start := (v.end + 1) &&& max
    let stop := (v.end + count) &&& max
    some (start,.Initialized (value := niche.value) (validRange := v.withEnd stop))
  let distanceEndZero := max - v.end
  if count == 1 && v != (⟨0,1⟩ : WrappingRange) then
    let nextUp ← size.signExtend (v.end + 1) |>.mapError reprStr
    let nextDown ← size.signExtend (v.start - 1) |>.mapError reprStr
    return if nextDown.natAbs ≤ nextUp.natAbs then moveStart else moveEnd
  else if v.start.toNat > v.end.toNat then return moveEnd
  else if v.start.toNat ≤ distanceEndZero.toNat then
    return if count.toNat ≤ v.start.toNat then moveStart else moveEnd
  else
    let stop := (v.end + count) &&& max
    let overshotZero := 1 ≤ stop.toNat && stop.toNat ≤ v.end.toNat
    return if overshotZero then moveStart else moveEnd

end Miri.ABI.NicheLayout
