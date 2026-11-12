import Lean
/-! Pinned ty/consts/int.rs::ConstInt Debug, non-alternate mode used by generic
constant arguments. Values are ScalarInt raw bits, not host machine integers. -/
namespace Miri.Input.ConstIntegerPrinter
def scalar (signed pointerSized : Bool) (bytes raw : Nat) : Except String String := do
  unless [1,2,4,8,16].contains bytes do throw "unsupported ScalarInt integer width"
  let width := bytes * 8
  unless raw < 2^width do throw "ScalarInt bits exceed declared width"
  let name := if pointerSized then (if signed then "isize" else "usize")
    else (if signed then "i" else "u") ++ toString width
  if signed then
    let midpoint := 2^(width-1)
    if raw == midpoint then return name ++ "::MIN"
    if raw == midpoint-1 then return name ++ "::MAX"
    let value := if raw >= midpoint then (Int.ofNat raw - Int.ofNat (2^width)) else Int.ofNat raw
    pure (toString value)
  else
    if raw == 2^width-1 then return name ++ "::MAX"
    pure (toString raw)

def boolean (bytes raw : Nat) : Except String String := do
  unless bytes == 1 do throw "Bool ScalarInt width is not one byte"
  match raw with
  | 0 => pure "false" | 1 => pure "true"
  | _ => throw "Bool ScalarInt is not TRUE/FALSE"
end Miri.Input.ConstIntegerPrinter
