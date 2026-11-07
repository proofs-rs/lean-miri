import Miri.Input.Decoder
import Miri.Input.RuntimeProgram

open Miri.Input
private def must {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

def main : IO Unit := do
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile "examples/empty_function/input.json"))
  let owner ← must (RuntimeProgram.ofProgram (← must (lowerCoreProgram decoded.document)))
  let replacement := {owner.program with input := {owner.input with raw := .str "unrelated"}}
  let updated := owner.withProgram replacement
  unless updated.runtime.source.raw == owner.input.raw && updated.program.input.raw == owner.input.raw do
    throw (IO.userError "lowered view replacement changed the shared source owner")
  IO.println "single owner source preservation PASS"
