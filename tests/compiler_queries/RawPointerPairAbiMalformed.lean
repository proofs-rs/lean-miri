import Miri.Input.Decoder
import Miri.Input.CompilerInstanceAbi

open Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected raw pointer pair fixture")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let mut checked := false
  for source in document.instances do
    let .Item definition := source.instanceKind | continue
    unless (document.definitions[definition]?.bind (·.rawPath) |>.bind
        (fun p => p.components.back?.bind (·.name))) == some "identity" do continue
    let (abi,after) ← must ((WorldInstanceAbi.construct source.id #[]).run world)
    let layout := abi.ret.layout
    let .Arbitrary offsets order := layout.layout.fields | continue
    unless offsets.size == 2 do continue
    let _ ← must ((WorldAggregateAbi.rawPointerPair runtime layout).run after)
    let malformed := #[
      {layout with layout := {layout.layout with fields := .Arbitrary #[] order}},
      {layout with layout := {layout.layout with fields := .Arbitrary #[⟨100⟩,⟨100⟩] order}},
      {layout with layout := {layout.layout with fields := .Arbitrary #[⟨0⟩,⟨0⟩] order}},
      {layout with layout := {layout.layout with size := ⟨17⟩}},
      {layout with layout := {layout.layout with backendRepr := .Memory (sized := true)}}]
    for bad in malformed do
      if ((WorldAggregateAbi.rawPointerPair runtime bad).run after).isOk then
        throw (IO.userError "malformed raw pointer pair layout was accepted")
    checked := true
    break
  unless checked do throw (IO.userError "missing raw pointer pair control")
  IO.println "PASS valid raw pointer pair; five malformed physical layouts rejected"
