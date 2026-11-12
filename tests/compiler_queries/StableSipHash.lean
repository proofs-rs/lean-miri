import Lean
import Miri.Input.StableSipHash
open Lean Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected pinned StableHasher oracle JSON")
  let rows ← must ((← must (Json.parse (← IO.FS.readFile path))).getArr?)
  unless rows.size == 265 do throw (IO.userError "incomplete StableHasher vector domain")
  for row in rows do
    let bytes ← (← must ((← must (row.getObjVal? "bytes")).getArr?)).mapM fun value => do
      let value ← must value.getNat?
      unless value < 256 do throw (IO.userError "oracle byte exceeds u8")
      pure (UInt8.ofNat value)
    let text ← must ((← must (row.getObjVal? "hash")).getStr?)
    let some expected := text.toNat? | throw (IO.userError "oracle hash is not decimal")
    let actual := StableSipHash.hash ⟨bytes⟩
    unless actual.toNat == expected do
      throw (IO.userError s!"stable SipHash differs at {bytes.size} input bytes")
  IO.println s!"PASS {rows.size} pinned StableHasher vectors, including tails and multi-block inputs"
