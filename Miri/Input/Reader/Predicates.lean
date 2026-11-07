import Miri.Input.Reader.Catalog
import Miri.Input.DecoderValues

namespace Miri.Input.Reader
open Lean

def Catalog.readPredicateDefinitions (catalog : Catalog) : Except String (Array CompilerPredicateEvidence) := do
  let values ← catalog.array (← catalog.field catalog.root "compiler_predicate_queries" "$") "compiler_predicate_queries"
  let mut result := #[]
  for (input,index) in values.toList.zipIdx do
    let path := s!"$.compiler_predicate_queries[{index}]"
    let natural := fun input key => do catalog.natural (← catalog.field input key path) path
    let text := fun input key => do catalog.string (← catalog.field input key path) path
    let id ← natural input "predicate_id"
    unless id == index do throw s!"{path}: predicate ID differs from its table position"
    let typingEnvironment ← text input "typing_env"
    unless typingEnvironment == "fully_monomorphized" do throw s!"{path}: invalid typing environment"
    let original ← catalog.field input "original" path
    unless (← natural original "predicate_id") == id do throw s!"{path}: predicate definition identity mismatch"
    let normalization ← catalog.field input "normalization" path
    let normalizedValue ← catalog.inspect (← catalog.field normalization "value" path) path
    let normalizedId ← if normalizedValue == .null then pure none else some <$> normalizedValue.getNat?
    if let some target := normalizedId then
      unless target < values.size do throw s!"{path}: invalid normalized predicate ID {target}"
    let kind := DecoderValues.vtablePredicateKind (← text original "kind")
    if let .unknown tag := kind then throw s!"{path}: unsupported predicate kind {tag}"
    let autoTrait ← catalog.boolean (← catalog.field input "auto_trait" path) path
    unless autoTrait == (kind == .autoTrait) do throw s!"{path}: predicate kind/auto-trait flag mismatch"
    let stableKey ← natural input "stable_key"
    unless stableKey < values.size do throw s!"{path}: invalid predicate comparison rank"
    result := result.push {
      id, typingEnvironment
      status := DecoderValues.parseStatus (← text original "status")
      kind, stableKey, autoTrait
      normalizationStatus := DecoderValues.parseStatus (← text normalization "status")
      normalizedId }
  return result

end Miri.Input.Reader
