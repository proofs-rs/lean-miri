import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata

open Miri.Input

private def must {α} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: RuntimeMetadataCacheBehavior <export.json>")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let metadata ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let some first := metadata.source.types[0]? | throw (IO.userError "empty source type graph")
  let some firstLayout := metadata.layouts[0]? | throw (IO.userError "empty layout table")
  let indexed := RuntimeMetadata.Indexed.ofMetadata metadata
  check ((metadata.node first.id).toOption.map (·.display) == some first.display)
    "canonical cached base node lookup failed"
  check (decide (metadata.lookup firstLayout.1 = indexed.lookup firstLayout.1))
    "canonical base/indexed layout lookup diverged"

  -- An ordinary update outside the indexed arrays preserves the caches safely.
  let rawUpdated : RuntimeMetadata := { metadata with source := { metadata.source with raw := .null } }
  check ((rawUpdated.node first.id).toOption.map (·.display) == some first.display)
    "source-only update invalidated a matching type cache"

  -- Explicitly clearing caches exercises the original linear-search fallback.
  let appended := { first with display := "LATER_DUPLICATE" }
  let manual : RuntimeMetadata := { metadata with
    source := { metadata.source with types := metadata.source.types.push appended }
    nodeCache := none
    layouts := metadata.layouts.push (first.id, .error (.invalid "later" "duplicate"))
    layoutCache := none
  }
  check ((manual.node first.id).toOption.map (·.display) == some first.display)
    "uncached base node lookup did not retain first duplicate"
  check ((manual.node first.id).toOption.map (·.display) ==
    ((RuntimeMetadata.Indexed.ofMetadata manual).node first.id).toOption.map (·.display))
    "uncached/indexed duplicate node lookup diverged"
  check (decide (manual.lookup first.id = (RuntimeMetadata.Indexed.ofMetadata manual).lookup first.id))
    "uncached/indexed duplicate layout lookup diverged"
  let missing := first.id + 1000000
  match manual.node missing with
  | .error (.missing _) => pure ()
  | _ => throw (IO.userError "uncached base node fallback accepted a missing key")
  match manual.lookup missing with
  | .error (.missing _) => pure ()
  | _ => throw (IO.userError "uncached base layout fallback accepted a missing key")

  -- The first matching failed row is observable; a later success cannot mask it.
  let firstError := RuntimeMetadataError.invalid "first" "must remain visible"
  let firstSuccess ← must ((metadata.lookup first.id).mapError toString)
  let badFirst : RuntimeMetadata := { manual with
    layouts := #[(first.id, .error firstError), (first.id, .ok firstSuccess)]
    layoutCache := none
  }
  check (decide (badFirst.lookup first.id = .error firstError))
    "base fallback did not preserve first matching layout error"
  check (decide (badFirst.lookup first.id = (RuntimeMetadata.Indexed.ofMetadata badFirst).lookup first.id))
    "indexed lookup masked first matching layout error"

  match RuntimeMetadata.ofDocument { decoded.document with types := decoded.document.types.push first } with
  | .error (.duplicateType id) => check (id == first.id) "duplicate type error ID changed"
  | _ => throw (IO.userError "duplicate compiler type ID accepted")

  IO.println s!"RuntimeMetadata cache behavior PASS: {metadata.source.types.size} decoded types; cached, fallback, first-wins and first-error behavior"
