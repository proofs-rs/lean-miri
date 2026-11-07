import MiriTests.Input.SharedPayloads
import Miri.Input.CompilerFacts

open Lean Miri Miri.Input

private def must (result : Except ε α) [ToString ε] : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

private def representation (raw : Json) (node : TypeNode) : Except String Json := do
  let types ← (← raw.getObjVal? "types").getArr?
  let some input := types[node.id]? | throw "type oracle absent"
  (← input.getObjVal? "shape").getObjVal? "representation"

private def sourceReprEqual (raw : Json) (left right : TypeNode) : Except String Bool := do
  let left ← representation raw left
  let right ← representation raw right
  let mut same := true
  for key in #["integer", "align_bytes", "pack_bytes", "flags_bits", "scalable_element"] do
    same := same && (← left.getObjVal? key) == (← right.getObjVal? key)
  return same

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: TypeShapeSemantics <export.json>")
  let text ← IO.FS.readFile path
  let decoded ← must (decodeRuntimeJson text)
  let oracle ← must (SharedPayloads.resolveGraph (← must (Json.parse text)))
  let runtime ← must (RuntimeMetadata.ofDocument decoded.document)
  let program ← must (lowerCoreProgram decoded.document)
  let cleanSource := {runtime.source with
    raw := .null
    sharedNodes := #[] }
  let clean := {runtime with source := cleanSource}
  let context := CompilerFacts.ofOwner {(← must (RuntimeProgram.ofProgram program)) with input := cleanSource}
  let adts := runtime.source.types.filter (fun node => node.shapeKind == .adt && node.shapeStatus == .supported)
  let mut comparisons := 0
  for left in adts do
    let expected ← must (representation oracle.root left)
    let actual ← must (clean.typeRepresentation left.id)
    unless actual.transparent == (← must ((← must (expected.getObjVal? "transparent")).getBool?)) &&
        actual.c == (← must ((← must (expected.getObjVal? "c")).getBool?)) &&
        actual.rust == (← must ((← must (expected.getObjVal? "rust")).getBool?)) &&
        actual.simd == (← must ((← must (expected.getObjVal? "simd")).getBool?)) do
      throw (IO.userError "representation flags changed")
    for right in adts do
      let expected ← must (sourceReprEqual oracle.root left right)
      let actual ← must (CompilerFacts.reprEqualUpToSeed context left.id right.id)
      unless actual == expected do throw (IO.userError "representation equivalence changed")
      comparisons := comparisons + 1
  unless comparisons > 0 do throw (IO.userError "fixture lacks ADTs")
  IO.println s!"typed representation semantics: PASS ({adts.size} ADTs; {comparisons} pairs; raw source removed)"
