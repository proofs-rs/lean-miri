import Lean
import Miri.ABI.PackedExternAbi
open Lean
private def checked (input : Json) : Except String Nat := do
  let rows ← input.getArr?
  unless rows.size == 40 do throw "pinned ABI oracle omitted variants"
  for (row,index) in rows.zipIdx do
    let packed ← (← row.getObjVal? "packed").getNat?
    unless packed == index do throw "pinned ABI enum order differs"
    let expected ← (← row.getObjVal? "spelling").getStr?
    let actual ← Miri.ABI.ExternAbi.ofPacked packed
    unless actual.asStr == expected do throw "ABI enum decoding/spelling differs from pinned rustc"
  for invalid in #[40,255,2^64-1] do
    unless (Miri.ABI.ExternAbi.ofPacked invalid).toOption.isNone do
      throw "packed ABI outside pinned enum accepted"
  pure rows.size

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected pinned ExternAbi oracle JSON")
  match Json.parse (← IO.FS.readFile path) >>= checked with
  | .ok count => IO.println s!"PASS {count} exact rustc packed ABI variants/source spellings; invalid encodings reject"
  | .error error => throw (IO.userError error)
