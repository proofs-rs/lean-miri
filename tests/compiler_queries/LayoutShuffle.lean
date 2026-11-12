import Miri.ABI.LayoutShuffle

open Miri.ABI.LayoutShuffle
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
def main : IO Unit := do
  for initial in ([0,1,42,0xffffffffffffffff,0x123456789abcdef0] : List UInt64) do
    for size in [0,1,2,3,4,7,12,16,37,100] do
      let (values,state) ← must (shuffle (List.range size).toArray (seed initial))
      let (next,_) := next32 state
      IO.println s!"{initial} {size}:{String.intercalate "," (values.toList.map toString)};next={next}"
