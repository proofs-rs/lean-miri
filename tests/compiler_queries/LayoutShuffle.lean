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
  for initial in ([0,1,42,0xffffffffffffffff,0x123456789abcdef0] : List UInt64) do
    for bound in ([1,2,3,65537,2147483649,0xffffffff] : List UInt32) do
      let (value,state) ← must (uniform32 (seed initial) bound)
      let (next,_) := next32 state
      IO.println s!"u32 {initial} {bound}:{value};next={next}"
    for bound in ([1,2,3,4294967297,9223372036854775809,0xffffffffffffffff] : List UInt64) do
      let (value,state) ← must (uniform64 (seed initial) bound)
      let (next,_) := next32 state
      IO.println s!"u64 {initial} {bound}:{value};next={next}"
