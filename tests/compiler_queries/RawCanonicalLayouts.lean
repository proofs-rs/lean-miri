import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata
open Miri.Input
private def must {α} [ToString ε] : Except ε α → IO α
  | .ok x => pure x | .error e => throw (IO.userError (toString e))
def main (args : List String) : IO Unit := do
  let [beforePath,afterPath] := args | throw (IO.userError "expected frozen before and raw-canonical after documents")
  let rawBefore ← must (Lean.Json.parse (← IO.FS.readFile beforePath))
  let rawAfter ← must (Lean.Json.parse (← IO.FS.readFile afterPath))
  let oldRows ← must ((← must (rawBefore.getObjVal? "types")).getArr?)
  let newRows ← must ((← must (rawAfter.getObjVal? "types")).getArr?)
  let before ← must (decodeJson (← IO.FS.readFile beforePath))
  let after ← must (decodeJson (← IO.FS.readFile afterPath))
  let a ← must ((RuntimeMetadata.ofDocument before.document).mapError toString)
  let b ← must ((RuntimeMetadata.ofDocument after.document).mapError toString)
  unless a.source.types.size == b.source.types.size do throw (IO.userError "raw type discovery changed")
  let mut checked := 0
  for old in a.source.types do
    let some new := b.source.types[old.id]? | throw (IO.userError "type identity disappeared")
    let some oldRow := oldRows[old.id]? | throw (IO.userError "old raw row absent")
    let some newRow := newRows[new.id]? | throw (IO.userError "new raw row absent")
    let oldShape ← must (oldRow.getObjVal? "shape")
    let newShape ← must (newRow.getObjVal? "shape")
    unless old.display == new.display && oldShape == newShape do
      throw (IO.userError s!"raw type identity or shape changed at {old.id}")
    let oldLayout ← must (a.lookup old.id |>.mapError toString)
    let newLayout ← must (b.lookup new.id |>.mapError toString)
    unless oldLayout == newLayout do throw (IO.userError s!"complete canonical layout changed: {old.id} {old.display}")
    checked := checked + 1
  IO.println s!"PASS {checked} exact raw type identities and complete canonical layouts preserved before/after exporter query elimination"
