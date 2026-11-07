import Miri.Input.Reader.RuntimeQueries

namespace Miri.Input.Reader.StartupQueryReader
open Lean

private def queryValue (catalog : Catalog) (query : Json) (path : String) : Except String Json := do
  let status ← catalog.string (← catalog.field query "status" path) path
  if status == "supported" then catalog.field query "value" path
  else if status == "unsupported" then
    throw ((do catalog.string (← catalog.field query "reason" path) path).toOption.getD
      "exact compiler startup query is unavailable")
  else throw s!"unknown compiler startup query status `{status}`"

/-- Independent startup queries retain demand-local failures. Source DefId
coordinates remain compiler metadata; the reader invents no item identity. -/
def read (catalog : Catalog) : Except String StartupQueryData := do
  let path := "$.compiler_runtime_queries.startup"
  let queries ← catalog.field catalog.root "compiler_runtime_queries" "$"
  let startup ← catalog.field queries "startup" path
  let noCore := do
    catalog.boolean (← queryValue catalog (← catalog.field startup "no_core" path) path) path
  let coreEscapeDefault := do
    let value ← queryValue catalog (← catalog.field startup "core_escape_default" path) path
    let definition ← catalog.field value "definition" path
    let source : DefinitionId := ⟨← catalog.natural (← catalog.field definition "crate" path) path,
      ← catalog.natural (← catalog.field definition "index" path) path⟩
    let available ← catalog.boolean (← catalog.field value "mir_available" path) path
    return (source,available)
  return ⟨noCore,coreEscapeDefault⟩

/-- Keep the source builder's missing/malformed distinctions while decoding
producer settings once at the transport boundary. -/
def panicUnwinds (catalog : Catalog) : Except String Bool := do
  let path := "$.producer.input_settings"
  let producer ← (catalog.field catalog.root "producer" "$").mapError fun _ =>
    "source compiler panic strategy is missing"
  let settings ← (catalog.field producer "input_settings" path).mapError fun _ =>
    "source compiler panic strategy is missing"
  let status ← (catalog.field settings "status" path).mapError fun _ =>
    "source compiler settings status is missing"
  let status ← (catalog.string status path).mapError fun _ =>
    "source compiler settings status is malformed"
  unless status == "supported" do throw "source compiler settings are not supported"
  let strategy ← (catalog.field settings "effective_panic_strategy" path).mapError fun _ =>
    "source compiler panic strategy is missing"
  let strategy ← (catalog.string strategy path).mapError fun _ =>
    "source compiler panic strategy is malformed"
  match strategy with
  | "unwind" => return true
  | "abort" | "immediate-abort" => return false
  | _ => throw s!"unknown source compiler panic strategy: {strategy}"

end Miri.Input.Reader.StartupQueryReader
