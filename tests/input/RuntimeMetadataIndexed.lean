import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata

open Miri.Input

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: RuntimeMetadataIndexed <export.json>")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let metadata ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let indexed := RuntimeMetadata.Indexed.ofMetadata metadata
  for node in metadata.source.types do
    let original ← must ((metadata.node node.id).mapError toString)
    let selected ← must ((indexed.node node.id).mapError toString)
    check (original.id == selected.id && original.display == selected.display &&
      original.payload.compress == selected.payload.compress)
      s!"indexed source node changed {node.id}"
    check (decide (metadata.lookup node.id = indexed.lookup node.id))
      s!"indexed layout result/error changed {node.id}"
  let missing := metadata.source.types.size + 1000000
  match metadata.node missing, indexed.node missing with
  | .error original, .error selected =>
    check (decide (original = selected)) "missing node error changed"
  | _, _ => throw (IO.userError "missing node unexpectedly resolved")
  check (decide (metadata.lookup missing = indexed.lookup missing)) "missing layout error changed"
  let some first := metadata.source.types[0]? | throw (IO.userError "empty type graph")
  let duplicate := {metadata.source with types := metadata.source.types.push first}
  match RuntimeMetadata.ofDocument duplicate with
  | .error (.duplicateType id) => check (id == first.id) "duplicate error changed"
  | _ => throw (IO.userError "duplicate source ID accepted")
  let appended := {first with display := "LATER_DUPLICATE"}
  let manual : RuntimeMetadata := {metadata with
    source := {metadata.source with types := metadata.source.types.push appended}
    layouts := metadata.layouts.push (first.id, .error (.invalid "later" "duplicate"))}
  let manualIndexed := RuntimeMetadata.Indexed.ofMetadata manual
  check ((manual.node first.id).toOption.map (·.display) ==
    (manualIndexed.node first.id).toOption.map (·.display))
    "manual duplicate node first-wins policy changed"
  check (decide (manual.lookup first.id = manualIndexed.lookup first.id))
    "manual duplicate layout first-wins policy changed"
  IO.println s!"RuntimeMetadata Indexed PASS: {metadata.source.types.size} node/layout results, missing errors, duplicate rejection and first-wins"
