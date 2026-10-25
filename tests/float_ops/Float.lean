import Miri.Interpreter.FloatOps
open Miri Miri.ABI Miri.Memory Miri.Interpreter
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000
private def half (n : Nat) : FloatBits := ⟨.binary16, BitVec.ofNat 128 n⟩
example : (half 15360).arithmetic .Add (half 15360) = .ok (half 16384) := by decide
example : (half 15360).arithmetic .Div (half 16384) = .ok (half 14336) := by decide
example : (half 15872).arithmetic .Rem (half 15360) = .ok (half 14336) := by decide
example : (half 32768).arithmetic .Add (half 32768) = .ok (half 32768) := by decide
example : (half 32768).arithmetic .Sub (half 0) = .ok (half 32768) := by decide
example : (half 15360).arithmetic .Sub (half 15360) = .ok (half 0) := by decide
example : (half 0).arithmetic .Mul (FloatBits.infinity .binary16) =
    .ok (FloatBits.preferredNaN .binary16) := by decide
example : (half 0).comparison .Eq (half 32768) = .ok true := by decide
example : (FloatBits.preferredNaN .binary16).comparison .Eq (half 0) = .ok false := by decide
example : (FloatBits.preferredNaN .binary16).comparison .Ne (half 0) = .ok true := by decide
example : FloatBits.roundRatio .binary16 false 1 (2^25) = .ok (half 0) := by decide
example : FloatBits.roundRatio .binary16 false 3 (2^25) = .ok (half 2) := by decide
example : FloatBits.fromInteger .binary16 65504 = .ok (half 31743) := by decide
example : FloatBits.fromInteger .binary16 65520 = .ok (FloatBits.infinity .binary16) := by decide
example : (half 48640).toInteger 8 true = .ok (-1) := by decide
example : (FloatBits.infinity .binary16).toInteger 8 true = .ok 127 := by decide
example : (FloatBits.infinity .binary16 true).toInteger 8 true = .ok (-128) := by decide
example : (FloatBits.infinity .binary16 true).toInteger 8 false = .ok 0 := by decide
example : (FloatBits.preferredNaN .binary16).toInteger 128 false = .ok 0 := by decide
example : (half 31745).negate = .ok (half 64513) := by decide
example : (half 31745).isSignaling = .ok true := by decide
example : FloatBits.nanChoices .binary16 [half 31745] false =
    .ok [FloatBits.preferredNaN .binary16] := by decide
example : FloatBits.nanChoices .binary16 [half 31745] true =
    .ok [half 32256, half 65024, half 32257, half 65025, half 31745, half 64513] := by decide

private def formats : List FloatFormat := [.binary16, .binary32, .binary64, .binary128]
private def randomPatterns (width : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | count + 1, seed =>
    let next := (seed * 47026247687942121848144207491837523525 + 117397592171526113268558934119004209487) % 2^width
    next :: randomPatterns width count next
private def corpus (f : FloatFormat) : List FloatBits :=
  let frac := f.fractionBits
  let sign := 2^(f.width-1)
  let inf := (2^f.exponentBits-1)*2^frac
  let one := f.bias*2^frac
  let values := [0, sign, 1, sign+1, 2^frac-1, 2^frac,
    one-1, one, one+1, one+2^(frac-1), one+2^frac,
    inf-1, inf, inf+1, inf+2^(frac-1), inf+2^(frac-1)+1,
    sign+inf, sign+inf+1, sign+one, sign+one+1]
  (values ++ randomPatterns f.width 8 81985529216486895).map fun n => ⟨f, BitVec.ofNat 128 n⟩
private def require (value : Except FloatError A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError s!"{repr error}")

/-- Deterministic corpus output for direct pinned-apfloat comparison. -/
def main : IO Unit := do
  for format in formats do
    let values := corpus format
    for left in values do
      for right in values do
        for op in [.Add, .Sub, .Mul, .Div, .Rem] do
          let value ← require (left.arithmetic op right)
          IO.println value.bits.toNat
        for op in [.Eq, .Ne, .Lt, .Le, .Gt, .Ge] do
          IO.println (if ← require (left.comparison op right) then 1 else 0)
    for value in values do
      IO.println (← require value.negate).bits.toNat
      for width in [8, 16, 32, 64, 128] do
        IO.println (← require (value.toInteger width true))
        IO.println (← require (value.toInteger width false))
      for target in formats do
        IO.println (← require (value.convert target)).bits.toNat
    for integer in [0, 1, -1, 2049, -2049, 65520, 16777217, 9007199254740993,
        170141183460469231731687303715884105727, -170141183460469231731687303715884105728] do
      IO.println (← require (FloatBits.fromInteger format integer)).bits.toNat

  for source in formats do
    for target in formats do
      let choices ← require (FloatBits.nanChoices target (corpus source) true)
      IO.println choices.length
      for value in choices do IO.println value.bits.toNat
      let fixed ← require (FloatBits.nanChoices target (corpus source) false)
      IO.println fixed.length
      for value in fixed do IO.println value.bits.toNat
