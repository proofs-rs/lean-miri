import Miri.Input.Reader.Generics

namespace Miri.Input.Reader.PatternReader
open Lean Miri.MIR
abbrev Decode := MIRReader.Decode

private def intern (value : PatternData) : Decode Nat := do
  let state ← get
  if let some id := state.patterns.idxOf? value then return id
  set {state with patterns := state.patterns.push value}
  return state.patterns.size

partial def pattern (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode Nat := do
  let slot ← catalog.readCached (·.patternReferences) (fun state patternReferences => {state with patternReferences})
    (fun input path => do
      catalog.requireSupported input path
      let value ← (show Decode PatternData from do
        match ← catalog.string (← catalog.field input "kind" path) path with
        | "range" =>
          let start ← GenericReader.constant catalog count (← catalog.field input "start" path) path
          let finish ← GenericReader.constant catalog count (← catalog.field input "end" path) path
          return .range start finish
        | "or" =>
          let children ← catalog.array (← catalog.field input "patterns" path) path
          return .or (← children.mapIdxM fun index value => pattern catalog count value s!"{path}.patterns[{index}]")
        | "not_null" => return .notNull
        | kind => throw s!"{path}: unknown pattern kind {kind}")
      intern value) input path
  let state ← get
  state.patternReferences.lookup slot |>.mapError (fun id => s!"{path}: invalid pattern ID {id}")

def types (catalog : Catalog) (count : Nat) : Decode (Array (Option Nat)) := do
  let values ← catalog.array (← catalog.field catalog.root "types" "$") "types"
  values.mapIdxM fun index input => do
    let path := s!"types[{index}].shape.pattern"
    let shape ← catalog.field input "shape" path
    match ← catalog.optionalField shape "pattern" path with
    | none | some .null => return none
    | some value => some <$> pattern catalog count value path

end Miri.Input.Reader.PatternReader
