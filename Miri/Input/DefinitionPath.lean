import Miri.Input.GenericMaterialCodec
import Miri.Input.GenericSyntax
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
inductive HeaderSafety where
  | normalSafe | normalUnsafe | safeTargetFeatures
  deriving Repr, DecidableEq, BEq
structure GenericHeader where
  parentParameterCount : Nat
  parameters : Array GenericSubstitution.ArgSort
  defaultExpressions : Array (Option GenericSubstitution.Term)
  deriving Repr, DecidableEq
structure Material where
  components : Array Component
  stableCrateId : UInt64
  genericHeader : Option GenericHeader
  functionHeaderSafety : Option HeaderSafety := none
  deriving Repr, DecidableEq

private def namedKind (kind : String) : Bool :=
  ["crate_root","type","value","macro","lifetime","opaque_lifetime",
    "anonymous_associated_type"].contains kind

private def readHeader (value : Lean.Json) : Except String GenericHeader := do
  for (key,_) in (← value.getObj?).toArray do
    unless ["parent_parameter_count","parameters","default_expressions"].contains key do
      throw s!"unknown raw generic header field {key}"
  let parent ← (← value.getObjVal? "parent_parameter_count").getNat?
  let parameters ← (← (← value.getObjVal? "parameters").getArr?).mapM fun value => do
    match ← value.getStr? with
    | "type" => pure GenericSubstitution.ArgSort.type
    | "region" => pure .region | "constant" => pure .constant
    | _ => throw "unknown raw generic parameter sort"
  let expressions ← (← (← value.getObjVal? "default_expressions").getArr?).mapM fun value => do
    if value == .null then pure none
    else some <$> GenericMaterialCodec.readTerm 16384 value
  unless parent + expressions.size == parameters.size do
    throw "raw generic parent/default parameter domain mismatch"
  for (expression,index) in expressions.zipIdx do
    if let some expression := expression then
      unless parameters[parent + index]? == some expression.sort do
        throw "raw generic default expression sort mismatch"
      GenericMaterialCodec.validateParameters parameters 16384 expression
      let role ← match expression.sort with
        | .type => pure GenericSyntax.Role.type
        | .region => pure .region | .constant => pure .constant
        | .aggregate => throw "raw generic default has aggregate sort"
      GenericSyntax.validate {parameters} 16384 role expression
  pure ⟨parent,parameters,expressions⟩

def read (value : Lean.Json) : Except String Material := do
  for (key,_) in (← value.getObj?).toArray do
    unless ["components","stable_crate_id","generic_header","function_header_safety"].contains key do
      throw s!"unknown raw definition path field {key}"
  let components ← (← (← value.getObjVal? "components").getArr?).mapM fun value => do
    for (key,_) in (← value.getObj?).toArray do
      unless ["kind", "name", "disambiguator"].contains key do
        throw s!"unknown raw definition path component field {key}"
    let kind ← (← value.getObjVal? "kind").getStr?
    let nameValue ← value.getObjVal? "name"
    let name ← if nameValue == .null then pure none else some <$> nameValue.getStr?
    unless ["crate_root","type","value","impl","foreign_module","constructor","use",
      "global_asm","macro","lifetime","closure","test_binder_constraints","anonymous_constant",
      "opaque_type","opaque_lifetime","anonymous_associated_type","synthetic_coroutine_body",
      "nested_static"].contains kind do
      throw "unknown raw DefPathData family"
    unless namedKind kind == name.isSome do
      throw "raw DefPathData family/name shape mismatch"
    let disambiguator ← (← value.getObjVal? "disambiguator").getNat?
    unless disambiguator < 2^32 do throw "raw definition disambiguator exceeds u32"
    pure (⟨kind,name,disambiguator⟩ : Component)
  let some root := components[0]? | throw "raw definition path is empty"
  unless root.kind == "crate_root" && root.disambiguator == 0 do
    throw "raw definition path has no canonical crate root"
  unless (components.extract 1 components.size).all (fun component => component.kind != "crate_root") do
    throw "raw definition path contains a nested crate root"
  let stable ← (← value.getObjVal? "stable_crate_id").getNat?
  unless stable < 2^64 do throw "raw stable crate identity exceeds u64"
  let header ← value.getObjVal? "generic_header"
  let header ← if header == .null then pure none else some <$> readHeader header
  let safetyValue ← value.getObjVal? "function_header_safety"
  let safety ← if safetyValue == .null then pure none else do
    let safety ← match ← safetyValue.getStr? with
      | "normal_safe" => pure HeaderSafety.normalSafe
      | "normal_unsafe" => pure HeaderSafety.normalUnsafe
      | "safe_target_features" => pure HeaderSafety.safeTargetFeatures
      | _ => throw "unknown raw function HeaderSafety"
    pure (some safety)
  pure ⟨components,UInt64.ofNat stable,header,safety⟩

def requireGenerics (path : Material) : Except String GenericHeader :=
  match path.genericHeader with
  | some header => pure header
  | none => throw "raw declaration generic header is unavailable"
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
