import Miri.ABI.Size

/-! Rustc's layout-randomization dependencies at
8144389c895da997dbdecaa635e41d6a50be6ffd: rand 0.9.3 (without `unbiased`),
rand_core 0.9.3 and rand_xoshiro 0.7.0. Source: xoshiro128starstar.rs,
splitmix64.rs/common.rs, seq/{slice,increasing_uniform}.rs and uniform_int.rs.
Copyright 2018–2023 Developers of the Rand project; MIT licensed port.
The exact crate checksums are recorded in the dependency source manifest. -/
namespace Miri.ABI.LayoutShuffle

structure Generator where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  deriving Repr, DecidableEq

private def rotate32 (value : UInt32) (shift : Nat) : UInt32 :=
  (value <<< UInt32.ofNat shift) ||| (value >>> UInt32.ofNat (32 - shift))

private def splitMix (seed : UInt64) : UInt64 × UInt64 := Id.run do
  let next := seed + 0x9e3779b97f4a7c15
  let value := (next ^^^ (next >>> 30)) * 0xbf58476d1ce4e5b9
  let value := (value ^^^ (value >>> 27)) * 0x94d049bb133111eb
  return (value ^^^ (value >>> 31), next)

def seed (value : UInt64) : Generator :=
  let (first,state) := splitMix value
  let (second,_) := splitMix state
  ⟨UInt32.ofNat first.toNat, UInt32.ofNat (first >>> 32).toNat,
    UInt32.ofNat second.toNat, UInt32.ofNat (second >>> 32).toNat⟩

def next32 (state : Generator) : UInt32 × Generator :=
  let result := rotate32 (state.b * 5) 7 * 9
  let t := state.b <<< 9
  let c := state.c ^^^ state.a
  let d := state.d ^^^ state.b
  let b := state.b ^^^ c
  let a := state.a ^^^ d
  (result,⟨a,b,c ^^^ t,rotate32 d 11⟩)

def next64 (state : Generator) : UInt64 × Generator :=
  let (lo,state) := next32 state
  let (hi,state) := next32 state
  (UInt64.ofNat lo.toNat ||| (UInt64.ofNat hi.toNat <<< 32),state)

/-- Canon's finite biased sample_single, as selected by pinned rand's features.
The extra draw on low-word overflow is semantically significant for shuffles. -/
def uniform32 (state : Generator) (bound : UInt32) : Except String (UInt32 × Generator) := do
  if bound == 0 then throw "empty shuffle sampling bound"
  let (value,state) := next32 state
  let product := value.toNat * bound.toNat
  let high := UInt32.ofNat (product / 2^32)
  let low := UInt32.ofNat product
  if low > (0 - bound) then
    let (next,state) := next32 state
    let newHigh := UInt32.ofNat (next.toNat * bound.toNat / 2^32)
    return (high + (if low.toNat + newHigh.toNat >= 2^32 then 1 else 0),state)
  return (high,state)

def uniform64 (state : Generator) (bound : UInt64) : Except String (UInt64 × Generator) := do
  if bound == 0 then throw "empty shuffle sampling bound"
  let (value,state) := next64 state
  let product := value.toNat * bound.toNat
  let high := UInt64.ofNat (product / 2^64)
  let low := UInt64.ofNat product
  if low > (0 - bound) then
    let (next,state) := next64 state
    let newHigh := UInt64.ofNat (next.toNat * bound.toNat / 2^64)
    return (high + (if low.toNat + newHigh.toNat >= 2^64 then 1 else 0),state)
  return (high,state)

private def chunkBoundAux (start product current : Nat) : Nat → Except String (UInt32 × Nat)
  | 0 => .error "shuffle chunk bound calculation exhausted"
  | fuel + 1 =>
    if product * current < 2^32 then
      chunkBoundAux start (product * current) (current + 1) fuel
    else .ok (UInt32.ofNat product,current - start)

private def chunkBound (start : Nat) : Except String (UInt32 × Nat) :=
  if start == 0 || start >= 2^32 then .error "invalid shuffle chunk starting bound"
  else chunkBoundAux start start (start + 1) 32

private def swap (values : Array α) (i j : Nat) : Except String (Array α) := do
  let some a := values[i]? | throw "shuffle source index out of bounds"
  let some b := values[j]? | throw "shuffle target index out of bounds"
  pure ((values.set! i b).set! j a)

/-- Full slice shuffle. The small-slice path preserves IncreasingUniform's
mixed-radix chunk consumption, including its zero-index first iteration. -/
def shuffle (values : Array α) (initial : Generator) : Except String (Array α × Generator) := do
  if values.size <= 1 then return (values,initial)
  let mut values := values
  let mut state := initial
  if values.size < 2^32 - 1 then
    let mut chunk : UInt32 := 0
    let mut remaining := 1
    for i in [:values.size] do
      let next := i + 1
      if remaining == 0 then
        let (bound,count) ← chunkBound next
        let (value,newState) ← uniform32 state bound
        chunk := value
        state := newState
        remaining := count
      remaining := remaining - 1
      let index := if remaining == 0 then chunk.toNat else chunk.toNat % next
      if remaining != 0 then chunk := chunk / UInt32.ofNat next
      unless index < values.size do throw "shuffle sampled index out of bounds"
      values ← swap values i index
  else
    for i in [:values.size] do
      unless i + 1 < 2^64 do throw "shuffle slice exceeds pinned host usize"
      let (index,newState) ← uniform64 state (UInt64.ofNat (i + 1))
      state := newState
      unless index.toNat < values.size do throw "shuffle sampled index out of bounds"
      values ← swap values i index.toNat
  return (values,state)

end Miri.ABI.LayoutShuffle
