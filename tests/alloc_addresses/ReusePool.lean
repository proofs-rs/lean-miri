import Miri.Memory.AllocAddresses.ReusePool

open Miri.ABI Miri.Concurrency Miri.Memory.AllocAddresses

private def sz (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def algn (exponent : Nat) : Align := ⟨exponent⟩

private def testClock (n : Fin 2147483648) : VClock :=
  VClock.ofList [VTimestamp.ofPacked (2 * n.val) (by omega)]

private def clockKey (clock : VClock) : Nat :=
  match clock.asList.head? with
  | none => 0
  | some timestamp => timestamp.time

private def showEntry (entry : ReusableAddress) : String :=
  s!"{entry.address}:{entry.size.bytes}:{entry.thread.toNat}:{clockKey entry.clock}"

private def showPool (pool : ReusePool) : String :=
  String.intercalate ";" ((List.range pool.pool.size).map fun index =>
    let entries := (pool.pool[index]?).getD #[]
    s!"{index}[{String.intercalate "," (entries.toList.map showEntry)}]")

private def compactFloat (value : Float) : String :=
  let trimmed := (toString value).toList.reverse.dropWhile (· == '0')
  let trimmed := match trimmed with
    | '.' :: rest => rest
    | _ => trimmed
  String.ofList trimmed.reverse

private def rateText (pool : ReusePool) : String :=
  s!"{compactFloat pool.addressReuseRate}:{compactFloat pool.addressReuseCrossThreadRate}"

private def makePool (rate cross : Float) : IO ReusePool := do
  match ReusePool.new ⟨rate, cross⟩ with
  | .ok pool => pure pool
  | .error error => throw (IO.userError (toString error))

private def emitAdd (tag : String) (pool : ReusePool) (choice : Bool)
    (address size : Nat) (alignExponent : Nat) (kind : AddressMemoryKind)
    (thread : Nat) (clockId : Fin 2147483648) : IO ReusePool := do
  let result := pool.addAddr choice (UInt64.ofNat address) (sz size)
      (algn alignExponent) kind (UInt32.ofNat thread)
      (fun _ => testClock clockId)
  let state := result.state
  IO.println s!"A {tag} {rateText state} {showPool state}"
  return state

private def emitTake (tag : String) (pool : ReusePool)
    (reuseChoice crossChoice : Bool) (selection size : Nat)
    (alignExponent : Nat) (kind : AddressMemoryKind) (thread : Nat) : IO ReusePool := do
  let result := pool.takeAddr reuseChoice crossChoice selection (sz size)
      (algn alignExponent) kind (UInt32.ofNat thread)
  let state := result.state
  let chosen := match result.outcome with
    | .error (.reusedAddressMisaligned ..) => "P"
    | .error _ => "E"
    | .ok none => "none"
    | .ok (some address) =>
        match address.clockToAcquire with
        | none => s!"{address.address}:same"
        | some clock => s!"{address.address}:clock{clockKey clock}"
  IO.println s!"T {tag} {chosen} {showPool state}"
  return state

def main : IO Unit := do
  let mut pool ← makePool 0.5 0.5
  pool ← emitAdd "size8-thread0" pool true 100 8 2 .other 0 ⟨11, by decide⟩
  pool ← emitAdd "size8-thread1" pool true 200 8 2 .other 1 ⟨22, by decide⟩
  pool ← emitAdd "size4-thread0" pool true 300 4 2 .other 0 ⟨33, by decide⟩
  pool ← emitAdd "align8-thread0" pool true 400 8 3 .other 0 ⟨44, by decide⟩
  pool ← emitAdd "stack-ignored" pool true 500 8 2 .stack 0 ⟨55, by decide⟩

  pool ← emitTake "cross-thread" pool true true 2 8 2 .other 2
  pool ← emitTake "same-thread" pool true false 1 8 2 .other 0
  pool ← emitTake "wrong-size" pool true true 0 16 2 .other 0
  pool ← emitTake "empty-subpool" pool true true 0 8 4 .other 0
  pool ← emitTake "stack-take" pool true true 0 8 2 .stack 0

  let mut skipped ← makePool 0.5 0.5
  skipped ← emitAdd "random-skip" skipped false 600 8 2 .other 0 ⟨66, by decide⟩

  let mut badAlignment ← makePool 1.0 0.0
  badAlignment ← emitAdd "bad-alignment-add" badAlignment true 101 8 1 .other 0
      ⟨77, by decide⟩
  badAlignment ← emitTake "bad-alignment-take" badAlignment true false 0 8 1 .other 0

  let mut shortage ← makePool 0.5 0.1
  IO.println s!"S before-shortage {rateText shortage}"
  shortage := shortage.addressSpaceShortage
  IO.println s!"S after-shortage {rateText shortage}"
  let disabled ← makePool 0.0 0.1
  IO.println s!"S disabled-shortage {rateText disabled.addressSpaceShortage}"

  let mut capped ← makePool 1.0 0.0
  for size in [1:66] do
    let result := capped.addAddr true (UInt64.ofNat (1000 + size)) (sz size)
        (algn 0) .other 0 (fun _ => VClock.default)
    capped := result.state
  IO.println s!"C cap-final {showPool capped}"

theorem bernoulli_zero_disallows_reuse :
    ReusePool.bernoulliChoiceAllowed 0.0 true = false := by
  decide

theorem bernoulli_one_requires_reuse :
    ReusePool.bernoulliChoiceAllowed 1.0 false = false := by
  decide
