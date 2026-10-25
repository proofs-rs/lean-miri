import Miri.Interpreter.IntrinsicX86.Aes
open Miri.ABI Miri.Interpreter.IntrinsicX86
private def random : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,seed =>
    let next := (seed*47026247687942121848144207491837523525+117397592171526113268558934119004209487)%2^128
    next :: random n next
private def corpus : List U128 :=
  ([0,2^128-1,1,2^127,0x00112233445566778899aabbccddeeff] ++ random 16 0x0123456789abcdef).map (BitVec.ofNat 128)
def main : IO Unit := do
  for block in corpus do
    for inverse in [false,true] do IO.println (Aes.mixColumns inverse block).toNat
    for key in corpus do
      for inverse in [false,true] do IO.println (Aes.round inverse block key).toNat
