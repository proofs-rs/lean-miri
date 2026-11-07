import Miri.Input.RuntimeMetadata

open Miri.Input

private def must {α} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: RuntimeMetadataIndexing <export.json>")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let metadata ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let some first := metadata.source.types[0]? | throw (IO.userError "empty source type table")
  for node in metadata.source.types do
    check ((metadata.node node.id).toOption.map (·.id) == some node.id) "wrong type row returned"
  let updated : RuntimeMetadata := {metadata with source := {metadata.source with
    types := metadata.source.types.set! 0 {first with display := "changed"}}}
  check ((updated.node 0).toOption.map (·.display) == some "changed") "lookup retained an old row"
  let misindexed : RuntimeMetadata := {metadata with source := {metadata.source with
    types := metadata.source.types.set! 0 {first with id := 1}}}
  match misindexed.node 0 with
  | .error (.invalid ..) => pure ()
  | _ => throw (IO.userError "misindexed type accepted")
  let error := RuntimeMetadataError.invalid "layout" "unavailable compiler result"
  let failed : RuntimeMetadata := {metadata with layouts := metadata.layouts.set! first.layoutId (some (.error error))}
  check (decide (failed.lookup 0 = .error error)) "stored layout error was masked"
  let wrongLayout : RuntimeMetadata := {metadata with source := {metadata.source with
    types := metadata.source.types.set! 0 {first with layoutId := metadata.layouts.size}}}
  match wrongLayout.lookup 0 with
  | .error (.invalid ..) => pure ()
  | _ => throw (IO.userError "invalid layout ID accepted")
  for result in #[metadata.node metadata.source.types.size |>.map (fun _ => ()),
      metadata.lookup metadata.layouts.size |>.map (fun _ => ())] do
    match result with
    | .error (.missing _) => pure ()
    | _ => throw (IO.userError "out-of-range metadata accepted")
  match RuntimeMetadata.ofDocument {decoded.document with types := decoded.document.types.push first} with
  | .error (.duplicateType 0) => pure ()
  | _ => throw (IO.userError "duplicate compiler type ID accepted")
  IO.println s!"metadata indexing: PASS ({metadata.source.types.size} types)"
