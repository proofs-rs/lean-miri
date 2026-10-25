import Miri.Memory.AllocAddresses.GlobalState

open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses

private def id1 : AllocId := ⟨1, by decide⟩
private def sz (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def asInt64 (n : Int) : Int64 := Int64.ofInt n

private def showLookup (result : Except AddressStateError (Option AllocId)) : String :=
  match result with
  | .error _ => "P"
  | .ok none => "none"
  | .ok (some id) => toString id.value

private def errored : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

private def makeState (mode : ProvenanceMode) (expose : Bool) :
    Except AddressStateError GlobalAddressState := do
  let state ← GlobalAddressState.new mode .managed 1000 2000 ⟨0.5, 0.1⟩
  let inserted := state.cacheAddress id1 1000
  let state ← match inserted.outcome with
    | .ok _ => pure inserted.state
    | .error error => throw error
  if expose then
    let result := state.exposeProvenance (.concrete id1 BorTag.one) (some true) false none
    match result.outcome with
    | .ok _ => pure result.state
    | .error error => throw error
  else pure state

def main : IO Unit := do
  let state ← match makeState .default true with
    | .ok state => pure state
    | .error error => throw (IO.userError (toString error))
  let hooks : AddressLookupHooks := {
    sizeOf := fun id => if id == id1 then some (sz 8) else none
    isLive := fun id => if id == id1 then some true else some false }
  for (label, address, size) in [
      ("exact", 1000, 0),
      ("interior", 1003, 0),
      ("end", 1008, 0),
      ("negative-end", 1008, -1),
      ("negative-base", 1000, -1)] do
    IO.println s!"L {label} {showLookup (state.allocIdFromAddr address (asInt64 size) hooks)}"
  let unexposed ← match makeState .default false with
    | .ok state => pure state
    | .error error => throw (IO.userError (toString error))
  IO.println s!"L unexposed {showLookup (unexposed.allocIdFromAddr 1003 (asInt64 1) hooks)}"
  let strict ← match makeState .strict true with
    | .ok state => pure state
    | .error error => throw (IO.userError (toString error))
  IO.println s!"L strict {if errored (strict.allocIdFromAddr 1000 (asInt64 0) hooks) then "P" else "O"}"

theorem source_negative_access_moves_left :
    (1000 : UInt64) - (1 : UInt64) = 999 := by decide
