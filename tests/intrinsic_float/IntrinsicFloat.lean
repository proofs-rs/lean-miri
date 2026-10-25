import Miri.Interpreter.IntrinsicFloat
open Miri.Interpreter
set_option maxRecDepth 30000
private def corpus (f : FloatFormat) : List FloatBits :=
  let frac := f.fractionBits
  let sign := 2^(f.width-1)
  let inf := (2^f.exponentBits-1)*2^frac
  let one := f.bias*2^frac
  [0,sign,1,sign+1,2^frac-1,2^frac,one-1,one,one+1,one+2^(frac-1),
    sign+one,sign+one+2^(frac-1),inf-1,inf,sign+inf,inf+1,inf+2^(frac-1)] |>.map fun n => ⟨f,BitVec.ofNat 128 n⟩
private def output (x : Except FloatError FloatBits) : IO Unit :=
  match x with
  | .ok x => IO.println x.bits.toNat
  | .error e => throw (IO.userError s!"{repr e}")
def main : IO Unit := do
  for f in [FloatFormat.binary16,.binary32,.binary64,.binary128] do
    let values := corpus f
    for a in values do
      for mode in [FloatIntegralRound.floor,.ceil,.trunc,.away,.even] do
        output (IntrinsicFloat.roundIntegral a mode)
      for b in values do
        for rightEqual in [false,true] do
          for op in [FloatMinMax.minimum,.maximum,.minimumNumber,.maximumNumber] do
            output (IntrinsicFloat.minMax a b op rightEqual)
        for c in values do
          output (IntrinsicFloat.fusedMulAdd a b c)
