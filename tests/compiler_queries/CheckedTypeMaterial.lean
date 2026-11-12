import Miri.Input.TypeArenaWorld

/-! The shared prefix is immutable raw syntax/index evidence, not a second
runtime arena. Reusing it starts separate empty constructor stores. -/
open Miri.Input Miri.Input.TypeArena
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def types : Array TypeNode := #[
  {id := 0, display := "ignored", layoutId := 0, shape := .uint (.known .u8)}]
private def definitions : Array DefinitionId := #[{crateIndex := 1,index := 7},{crateIndex := 2,index := 4}]

def main : IO Unit := do
  let checked ← must (CheckedMaterial.create types #[] definitions 8)
  unless (← must (checked.definitionRef ⟨2,4⟩)) == 1 do
    throw (IO.userError "checked physical definition index returned a different source row")
  if (checked.definitionRef ⟨2,5⟩).isOk then throw (IO.userError "absent physical definition was accepted")
  if (CheckedMaterial.create types #[] #[{crateIndex := 1,index := 7},{crateIndex := 1,index := 7}] 8).isOk then
    throw (IO.userError "duplicate raw physical identities were accepted")
  if (CheckedMaterial.create types #[] definitions 0).isOk then
    throw (IO.userError "zero raw pointer width was accepted")
  let bad := types.set! 0 {id := 3,display := "ignored",layoutId := 0,shape := .uint (.known .u8)}
  if (CheckedMaterial.create bad #[] definitions 8).isOk then
    throw (IO.userError "non-dense material source table was accepted")
  let initial := World.ofCheckedMaterial checked
  let (id,updated) ← must ((World.internType (.tuple #[0,0])).run initial)
  unless id == 1 && updated.constructedTypes.size == 1 do
    throw (IO.userError "checked prefix runtime construction was not dense")
  let independent := World.ofCheckedMaterial checked
  unless independent.constructedTypes.isEmpty && !(independent.lookupType id).isOk do
    throw (IO.userError "immutable prefix shared constructed runtime state across executions")
  unless (← must (updated.definitionRef ⟨2,4⟩)) == 1 do
    throw (IO.userError "constructor append changed raw definition identity")
  IO.println "PASS checked raw prefix/index, source guards, dense construction and execution isolation"
