import Lean
import Miri.Input.JsonReader

/-! Raw DefKey chain, declaration generic headers and symbols. No resolved or
trimmed display path is serialized here. -/
namespace Miri.Input.DefinitionPath
structure Component where
  kind : String
  name : Option String
  disambiguator : Nat
  deriving Repr, DecidableEq
structure Material where
  components : Array Component
  parentParameterCount : Nat
  parameterDefaults : Array Bool
  deriving Repr, DecidableEq

def read (value : Lean.Json) : Except String Material := do
  for (key,_) in (← value.getObj?).toArray do
    unless ["components", "parent_parameter_count", "parameter_defaults"].contains key do
      throw s!"unknown raw definition path field {key}"
  let components ← (← (← value.getObjVal? "components").getArr?).mapM fun value => do
    for (key,_) in (← value.getObj?).toArray do
      unless ["kind", "name", "disambiguator"].contains key do
        throw s!"unknown raw definition path component field {key}"
    let kind ← (← value.getObjVal? "kind").getStr?
    let nameValue ← value.getObjVal? "name"
    let name ← if nameValue == .null then pure none else some <$> nameValue.getStr?
    unless ["crate_root", "type", "value", "impl", "foreign_module", "constructor", "unsupported"].contains kind do
      throw "unknown raw DefPathData family"
    if ["crate_root", "type", "value"].contains kind && name.isNone then
      throw "named DefPathData component has no source symbol"
    pure (⟨kind,name,← (← value.getObjVal? "disambiguator").getNat?⟩ : Component)
  let defaults ← (← (← value.getObjVal? "parameter_defaults").getArr?).mapM Lean.Json.getBool?
  pure ⟨components,← (← value.getObjVal? "parent_parameter_count").getNat?,defaults⟩
def decode : JsonReader.Parser Material :=
  do JsonReader.liftExcept (read (← Lean.Json.Parser.anyCore))
end Miri.Input.DefinitionPath

namespace Miri.Input.DefinitionPath
/-- Exact local named-namespace branch of default_print_def_path. External
visible-parent paths, trimming, implementation and anonymous scopes require
separate source algorithms and never reuse a formatted type answer. -/
def localNamedPath (material : Material) (verbose trimDiagnostic trimmed : Bool) : Except String String := do
  if verbose then throw "verbose definition-path printing is not implemented"
  if trimDiagnostic && trimmed then throw "trimmed definition-path selection is not implemented"
  let some root := material.components[0]? | throw "raw definition path is empty"
  unless root.kind == "crate_root" do throw "raw definition path has no crate root"
  let mut names := #[]
  for component in material.components.extract 1 material.components.size do
    unless component.kind == "type" || component.kind == "value" do
      throw "definition-path printing requires an unsupported namespace branch"
    let some name := component.name | throw "named definition-path component has no symbol"
    if name.isEmpty then throw "definition-path component symbol is empty"
    if ["as", "async", "await", "become", "box", "break", "const", "continue", "crate",
      "do", "dyn", "else", "enum", "extern", "false", "final", "fn", "for", "gen", "if",
      "impl", "in", "let", "loop", "macro", "match", "mod", "move", "mut", "override",
      "priv", "pub", "ref", "return", "self", "Self", "static", "struct", "super", "trait",
      "true", "try", "type", "typeof", "unsafe", "unsized", "use", "virtual", "where",
      "while", "yield", "abstract"].contains name then
      throw "raw-identifier definition-path printing is not implemented"
    names := names.push name
  if names.isEmpty then throw "named definition path has no item component"
  pure (String.intercalate "::" names.toList)
end Miri.Input.DefinitionPath
