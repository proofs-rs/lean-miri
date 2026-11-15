import Lean
import Miri.Input.Model.SourceDeclarations

/-! Finite declaration source for the fixed foreign provider. The traversal is
pinned helpers.rs::iter_exported_symbols: local used/extern HIR definitions,
then linked dependency NonGeneric exports, excluding FFI reexports. The raw
symbol gate precedes generic inspection, as in lookup_exported_symbol.

This adapter computes no winning symbol, Instance, body or ABI. Attribute-based
name construction and weak/strong selection belong to the demand provider.
Opaque BytePos/hygiene/parent identities are preserved in declaration spans. -/
namespace Miri.Frontend.Foundation
open Lean
namespace ForeignDeclarationSource

private def rawDefinition (source : Json) : Except String Miri.Input.DefinitionId := do
  let crate ← source.getObjValAs? Nat "crate_index"
  let index ← source.getObjValAs? Nat "definition_index"
  unless crate < 2^32 && index < 2^32 do throw "foreign declaration DefId exceeds rustc index width"
  return ⟨crate,index⟩

private def attributes (item : Json) : Except String Miri.Input.SourceSymbols.Attributes := do
  let linkage ← item.getObjValAs? (Option String) "symbol_linkage"
  if let some linkage := linkage then
    unless #["External","AvailableExternally","LinkOnceAny","LinkOnceODR","WeakAny","WeakODR",
        "Appending","Internal","Private","ExternalWeak","Common"].contains linkage do
      throw "foreign declaration linkage source unsupported"
  return {
    symbolName := ← item.getObjValAs? (Option String) "symbol_name"
    itemName := ← item.getObjValAs? (Option String) "item_name"
    noMangle := ← item.getObjValAs? Bool "no_mangle"
    stdInternalSymbol := ← item.getObjValAs? Bool "std_internal_symbol"
    linkage
    procMacroDeclarations := ← item.getObjValAs? Bool "proc_macro_declarations" }

private def explicit (attributes : Miri.Input.SourceSymbols.Attributes) : Bool :=
  attributes.symbolName.isSome || attributes.noMangle || attributes.stdInternalSymbol

/-- Shallow lexical source only. Validate every original slot and parent before
flattening; retain type/const slots for the provider's explicit mono rejection.
There is no empty fallback for missing generic declaration material. -/
private def parameters (definition : Miri.Input.DefinitionId) (item : Json) :
    Except String (Array Miri.Input.SourceSymbols.ParameterKind) := do
  let some layers ← item.getObjValAs? (Option (Array Json)) "generic_layers"
    | throw "foreign declaration generic source unavailable"
  unless !layers.isEmpty do throw "foreign declaration generic layers absent"
  let mut previous := none
  let mut seen : Array Miri.Input.DefinitionId := #[]
  let mut result := #[]
  let mut parameterDefinitions : Array Miri.Input.DefinitionId := #[]
  for layer in layers do
    let owner ← rawDefinition (← layer.getObjVal? "owner")
    unless !seen.contains owner && !(parameterDefinitions.contains owner) &&
        owner.crateIndex == definition.crateIndex do throw "foreign declaration generic owner identity/cycle mismatch"
    let rawParent ← layer.getObjValAs? (Option Json) "parent"
    let parent ← rawParent.mapM rawDefinition
    unless parent == previous && (← layer.getObjValAs? Nat "parent_count") == result.size do
      throw "foreign declaration lexical generic parent/count mismatch"
    for parameter in (← layer.getObjValAs? (Array Json) "parameters") do
      unless (← parameter.getObjValAs? Nat "index") == result.size do
        throw "foreign declaration generic slot index mismatch"
      let parameterDefinition ← rawDefinition (← parameter.getObjVal? "definition")
      unless parameterDefinition.crateIndex == owner.crateIndex && parameterDefinition != owner &&
          !(seen.contains parameterDefinition) && !(parameterDefinitions.contains parameterDefinition) do
        throw "foreign declaration generic parameter identity mismatch"
      parameterDefinitions := parameterDefinitions.push parameterDefinition
      let kind ← match ← parameter.getObjValAs? String "kind" with
        | "region" => pure Miri.Input.SourceSymbols.ParameterKind.region
        | "type" => pure .typeParameter
        | "const" => pure .constParameter
        | _ => throw "foreign declaration generic parameter kind unsupported"
      result := result.push kind
    seen := seen.push owner
    previous := some owner
  unless previous == some definition do throw "foreign declaration generic terminal owner mismatch"
  return result

private def span (item : Json) : Except String Miri.Input.SourceSymbols.Span := do
  let key ← item.getObjVal? "source_span_key"
  let source ← item.getObjVal? "source_span"
  let start ← source.getObjVal? "start"
  let finish ← source.getObjVal? "end"
  let result : Miri.Input.SourceSymbols.Span := {
    isDummy := ← source.getObjValAs? Bool "is_dummy"
    lo := ← key.getObjValAs? Nat "lo"
    hi := ← key.getObjValAs? Nat "hi"
    context := ← key.getObjValAs? String "ctxt"
    parentLocalDefinition := ← key.getObjValAs? (Option Nat) "parent_local_definition"
    file := ← source.getObjValAs? String "file"
    startLine := ← start.getObjValAs? Nat "line"
    startColumn := ← start.getObjValAs? Nat "column"
    endLine := ← finish.getObjValAs? Nat "line"
    endColumn := ← finish.getObjValAs? Nat "column" }
  unless result.lo ≤ result.hi && result.hi < 2^32 &&
      result.isDummy == (result.lo == 0 && result.hi == 0) do
    throw "foreign declaration source span bounds/dummy mismatch"
  unless result.startLine ≤ result.endLine &&
      (result.startLine != result.endLine || result.startColumn ≤ result.endColumn) do
    throw "foreign declaration source span positions reversed"
  if let some parent := result.parentLocalDefinition then
    unless parent < 2^32 do throw "foreign declaration span parent exceeds rustc index width"
  unless !result.file.isEmpty && result.context.startsWith "#" &&
      (result.context.drop 1).toString.toNat?.isSome do throw "foreign declaration source span identity unavailable"
  return result

private def candidate (item : Json) (ordinal : Nat) (used : Bool)
    (crate : Nat) (crateName : String) (builtins : Bool) :
    Except String (Option Miri.Input.SourceSymbols.Declaration) := do
  let attrs ← attributes item
  if !explicit attrs then return none
  let definition ← rawDefinition item
  let kind ← item.getObjValAs? String "symbol_kind"
  unless #["function","associated_function","static","other"].contains kind do
    throw "foreign declaration source kind unsupported"
  let path ← item.getObjValAs? String "definition_path"
  unless !path.isEmpty do throw "foreign declaration source path absent"
  let declaration : Miri.Input.SourceSymbols.Declaration := {
    iterationIndex := ordinal, used, definition, path, kind
    crateIndex := crate, crateName, compilerBuiltins := builtins
    attributes := attrs, span := ← span item, parameters := ← parameters definition item }
  return some declaration

/-- Materialize the complete ordered explicit candidate declarations. Original
callback ordinals retain gaps for used/extern items without explicit symbols.
An executable format is mandatory even for a genuinely empty candidate result.
No body/instance identity is allocated; unsupported name attributes remain raw
source for the fixed provider's demand-time error, never a fabricated miss. -/
def derive (document : Json) : Except String Miri.Input.SourceSymbols.Material := do
  let graph ← document.getObjVal? "link_section_material"
  let localCrate ← graph.getObjValAs? Nat "local_crate"
  unless localCrate == 0 do throw "foreign declaration local crate differs from pinned LOCAL_CRATE"
  let localName ← graph.getObjValAs? String "local_crate_name"
  unless !localName.isEmpty do throw "foreign declaration local crate name absent"
  let localBuiltins ← graph.getObjValAs? Bool "local_compiler_builtins"
  let some dependencies ← graph.getObjValAs? (Option (Array Json)) "executable_dependencies"
    | throw "foreign declaration executable dependency format unavailable"
  let frames ← document.getObjVal? "frame_metadata"
  unless (← frames.getObjValAs? Nat "local_crate") == localCrate do
    throw "foreign source local/frame crate mismatch"
  let crates ← frames.getObjValAs? (Array Json) "crates"
  unless crates.size == dependencies.size do
    throw "foreign dependency format does not cover the finite crate universe"
  for index in [:crates.size] do
    let some crate := crates[index]? | throw "foreign frame crate source absent"
    let some dependency := dependencies[index]? | throw "foreign dependency crate source absent"
    unless (← crate.getObjValAs? Nat "crate") == index &&
        (← crate.getObjValAs? String "name") == (← dependency.getObjValAs? String "crate_name") do
      throw "foreign traversal/frame crate provenance mismatch"
  let mut declarations := #[]
  let mut ordinal := 0
  for item in (← graph.getObjValAs? (Array Json) "local_items") do
    unless (← rawDefinition item).crateIndex == localCrate do
      throw "foreign local declaration belongs to a different crate"
    let used := (← item.getObjValAs? Bool "used_compiler") || (← item.getObjValAs? Bool "used_linker")
    if used || (← item.getObjValAs? Bool "extern_indicator") then
      if let some declaration ← candidate item ordinal used localCrate localName localBuiltins then
        declarations := declarations.push declaration
      ordinal := ordinal + 1
  for index in [:dependencies.size] do
    let some dependency := dependencies[index]? | throw "foreign dependency source absent"
    unless (← dependency.getObjValAs? Nat "crate_index") == index && index < 2^32 do
      throw "foreign executable dependency indices not dense"
    let linkage ← dependency.getObjValAs? String "linkage"
    unless #["NotLinked","Static","Dynamic","IncludedFromDylib"].contains linkage do
      throw "foreign executable dependency linkage unsupported"
    let exports ← dependency.getObjValAs? (Array Json) "exports"
    let crateName ← dependency.getObjValAs? String "crate_name"
    let builtins ← dependency.getObjValAs? Bool "compiler_builtins"
    unless !crateName.isEmpty do throw "foreign dependency crate name absent"
    if index == localCrate then
      unless crateName == localName && builtins == localBuiltins do
        throw "foreign local/dependency crate provenance mismatch"
    if index == localCrate || linkage == "NotLinked" then
      unless exports.isEmpty do throw "foreign unlinked dependency has export source rows"
    else
      for exported in exports do
        match ← exported.getObjValAs? String "kind" with
        | "other" => pure ()
        | "non_generic" =>
          unless (← exported.getObjValAs? Bool "is_foreign") do
            if let some declaration ← candidate (← exported.getObjVal? "item") ordinal
                (← exported.getObjValAs? Bool "used") index crateName builtins then
              declarations := declarations.push declaration
            ordinal := ordinal + 1
        | _ => throw "foreign dependency export source kind unsupported"
  let source ← document.getObjVal? "foreign_symbol_material"
  let namespacePrefix ← source.getObjValAs? String "internal_symbol_namespace"
  unless namespacePrefix.startsWith "_RNvC" && namespacePrefix.endsWith "7___rustc" do
    throw "foreign source internal symbol namespace unsupported"
  return ⟨namespacePrefix,declarations⟩

/-- Project callable identity headers and their original lexical generic layers
from the same checked complete symbolic traversal. This allocates no instances
and supplies no ordinary/executable role. -/
def itemSource (document : Json) : Except String
    (Array Miri.Input.SourceDeclarations.ItemDeclaration × Array Miri.Input.SourceDeclarations.GenericLayer) := do
  let material ← derive document
  let graph ← document.getObjVal? "link_section_material"
  let mut items ← graph.getObjValAs? (Array Json) "local_items"
  let some dependencies ← graph.getObjValAs? (Option (Array Json)) "executable_dependencies"
    | throw "foreign declaration executable dependency format unavailable"
  for dependency in dependencies do
    for exported in (← dependency.getObjValAs? (Array Json) "exports") do
      if (← exported.getObjValAs? String "kind") == "non_generic" then
        items := items.push (← exported.getObjVal? "item")
  let callables := material.declarations.filter fun declaration =>
    declaration.kind == "function" || declaration.kind == "associated_function"
  if callables.isEmpty then return (#[],#[])
  -- Decode each raw identity once. Lists retain traversal order and duplicate
  -- rows, so all original lexical consistency checks still run below.
  let mut byDefinition : Std.HashMap (Nat × Nat) (Array Json) := {}
  for item in items do
    let definition ← rawDefinition item
    let key := (definition.crateIndex,definition.index)
    byDefinition := byDefinition.insert key (((byDefinition[key]?).getD #[]).push item)
  let mut declarations := #[]
  let mut layers : Array Miri.Input.SourceDeclarations.GenericLayer := #[]
  for declaration in callables do
    let kind : Miri.Input.SourceDeclarations.ItemKind :=
      if declaration.kind == "function" then .function else .associatedFunction
    let key := (declaration.definition.crateIndex,declaration.definition.index)
    let some matching := byDefinition[key]? | throw "foreign callable lexical source missing"
    for item in matching do
      -- derive checked the lexical chain while producing declaration.parameters.
      let some originals ← item.getObjValAs? (Option (Array Json)) "generic_layers"
        | throw "foreign callable generic layers unavailable"
      for original in originals do
        let owner ← rawDefinition (← original.getObjVal? "owner")
        let parent ← (← original.getObjValAs? (Option Json) "parent").mapM rawDefinition
        let params ← (← original.getObjValAs? (Array Json) "parameters").mapM fun parameter => do
          let kind ← match ← parameter.getObjValAs? String "kind" with
            | "region" => pure Miri.Input.SourceSymbols.ParameterKind.region
            | "type" => pure .typeParameter
            | "const" => pure .constParameter
            | _ => throw "foreign callable generic kind unsupported"
          let definition ← rawDefinition (← parameter.getObjVal? "definition")
          let index ← parameter.getObjValAs? Nat "index"
          return ({definition,index,kind} : Miri.Input.SourceDeclarations.GenericParameter)
        let parentCount ← original.getObjValAs? Nat "parent_count"
        let flattened := declaration.parameters.extract 0 (parentCount + params.size)
        let layer : Miri.Input.SourceDeclarations.GenericLayer :=
          ⟨owner,parent,parentCount,params,flattened⟩
        if let some old := layers.find? (·.owner == owner) then
          unless old == layer do throw "foreign callable lexical declaration conflict"
        else layers := layers.push layer
    let item : Miri.Input.SourceDeclarations.ItemDeclaration := {
      definition := declaration.definition,path := declaration.path,kind,parameters := declaration.parameters }
    if let some old := declarations.find? (·.definition == item.definition) then
      unless old == item do throw "foreign callable declaration conflict"
    else declarations := declarations.push item
  return (declarations,layers)

end ForeignDeclarationSource

def foreignDeclarations (document : Json) : Except String Miri.Input.SourceSymbols.Material :=
  ForeignDeclarationSource.derive document

end Miri.Frontend.Foundation
