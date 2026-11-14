import Miri.ABI.Size
/-! Byte-compatible `rustc-stable-hash`0.1.2 StableSipHasher128:
SipHash128-1-3 with zero keys. Upstream archive SHA256
781442f29170c5c93b7185ad559492601acdc71d5bb0706f5868094f45cfcd08.
The byte traversal owns only this demand's state and uses no shared cache. -/
namespace Miri.Input.StableSipHash
private structure State where
  a : UInt64
  b : UInt64
  c : UInt64
  d : UInt64
private def rotate (value : UInt64) (bits : UInt64) : UInt64 :=
  (value <<< bits) ||| (value >>> (64 - bits))
private def round (s : State) : State := Id.run do
  let a := s.a + s.b
  let b := rotate s.b 13 ^^^ a
  let a := rotate a 32
  let c := s.c + s.d
  let d := rotate s.d 16 ^^^ c
  let a := a + d
  let d := rotate d 21 ^^^ a
  let c := c + b
  let b := rotate b 17 ^^^ c
  pure ⟨a,b,rotate c 32,d⟩
private def rounds (s : State) : State := round (round (round s))
private def compress (s : State) (value : UInt64) : State :=
  let s := round {s with d := s.d ^^^ value}
  {s with a := s.a ^^^ value}
def hash (bytes : ByteArray) : Miri.ABI.U128 := Id.run do
  let mut s : State := ⟨0x736f6d6570736575,0x646f72616e646f6d ^^^ 0xee,
    0x6c7967656e657261,0x7465646279746573⟩
  let mut block : UInt64 := 0
  let mut pending : UInt64 := 0
  for byte in bytes.data do
    block := block ||| (byte.toUInt64 <<< (pending * 8))
    pending := pending + 1
    if pending == 8 then
      s := compress s block
      pending := 0
      block := 0
  let tail := block ||| ((UInt64.ofNat bytes.size &&& 255) <<< 56)
  s := compress s tail
  s := rounds {s with c := s.c ^^^ 0xee}
  let low := s.a ^^^ s.b ^^^ s.c ^^^ s.d
  s := rounds {s with b := s.b ^^^ 0xdd}
  let high := s.a ^^^ s.b ^^^ s.c ^^^ s.d
  pure (BitVec.ofNat 128 (low.toNat + high.toNat * 2^64))
end Miri.Input.StableSipHash
