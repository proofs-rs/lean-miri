import Miri.Input.Reader.Instances
import Miri.Input.Reader.Constants

namespace Miri.Input.Reader.MainQueryReader
open Lean
abbrev Decode := MIRReader.Decode

private def supported (catalog : Catalog) (query : Json) (path : String) : Except String Json := do
  unless (← catalog.string (← catalog.field query "status" path) path) == "supported" do
    throw "main compiler query is unresolved"
  catalog.field query "value" path
private def typeId (catalog : Catalog) (count : Nat) (value : Json) (path : String) : Except String MIR.TyId := do
  let id ← catalog.natural (← catalog.field value "type_id" path) path
  unless id < count do throw "main compiler query references missing type"
  return id
private def optionalDefinition (catalog : Catalog) (value : Json) (path : String) : Decode (Option MIR.DefId) := do
  if (← catalog.inspect value path) == .null then return none
  return some (← RegionReader.definition catalog value path)

private def entryType (catalog : Catalog) (source : Json) (compilerEntry : Option MIR.DefId)
    (path : String) : Decode (Option (MIR.DefId × UInt8)) := do
  let some query ← catalog.optionalField source "compiler_entry_type" path |
    if compilerEntry.isSome then throw "rustc selected main lacks exact EntryFnType query" else return none
  let value ← supported catalog query path
  if (← catalog.inspect value path) == .null then
    if compilerEntry.isSome then throw "rustc selected main lacks exact EntryFnType"
    return none
  let raw ← catalog.field value "definition" path
  let id : DefinitionId := ⟨← catalog.natural (← catalog.field raw "crate" path) path,
    ← catalog.natural (← catalog.field raw "index" path) path⟩
  let state ← get
  let definition ← match state.compiler.definitions.idxOf? id with
    | some id => pure id
    | none => throw "main entry type definition absent from compiler table"
  unless compilerEntry == some definition do throw "rustc EntryFnType definition differs from compiler-selected entry"
  let kind ← catalog.string (← catalog.field value "kind" path) path
  unless kind == "rustc_main" do throw s!"unsupported rustc EntryFnType `{kind}`"
  let sigpipe ← catalog.natural (← catalog.field value "sigpipe" path) path
  unless sigpipe <= 255 do throw "rustc EntryFnType sigpipe does not fit u8"
  return some (definition,UInt8.ofNat sigpipe)

private def queries (catalog : Catalog) (typeCount allocationCount : Nat) : Decode MainQueryData := do
  let path := "$.compiler_main_queries"
  let source ← catalog.field catalog.root "compiler_main_queries" "$"
  unless (← catalog.string (← catalog.field source "typing_env" path) path) == "fully_monomorphized" do
    throw "main query environment mismatch"
  let start ← optionalDefinition catalog (← catalog.field source "start_lang_item" path) path
  let compilerEntry ← optionalDefinition catalog (← catalog.field source "compiler_entry" path) path
  let original ← get
  let compilerEntryType := (entryType catalog source compilerEntry path).run original |>.map (·.1)
  let mut entries := #[]
  for record in ← catalog.array (← catalog.field source "entries" path) path do
    let definition ← RegionReader.definition catalog (← catalog.field record "definition" path) path
    if entries.any (·.definition == definition) then throw "duplicate source main definition key"
    let parameters ← (← catalog.array (← catalog.field record "generic_parameters" path) path).mapM fun value => do
      match ← catalog.string value path with
      | "lifetime" => pure CompilerGenericParameter.lifetime
      | "type_parameter" => pure .typeParameter
      | "const_parameter" => pure .constParameter
      | _ => throw "unknown main generic parameter kind"
    let signature : Except String MainSignatureData := do
      let value ← supported catalog (← catalog.field record "signature_query" path) path
      return ⟨← catalog.boolean (← catalog.field value "has_bound_variables" path) path,
        ← catalog.boolean (← catalog.field value "output_has_bound_variables" path) path,
        ← typeId catalog typeCount (← catalog.field value "return_type" path) path,
        ← typeId catalog typeCount (← catalog.field value "function_pointer_type" path) path⟩
    let resolution : Decode (Option Miri.Interpreter.CallInstance) := do
      let value ← supported catalog (← catalog.field record "signature_query" path) path
      unless (← catalog.boolean (← catalog.field value "compiler_selected_entry" path) path) do
        throw "lang_start query not requested for a non-compiler-selected entry"
      let value ← supported catalog (← catalog.field value "start_resolution" path) path
      if (← catalog.inspect value path) == .null then return none
      return some (← InstanceReader.read catalog typeCount value path)
    let original ← get
    let outcome ← match resolution.run original with
      | .error reason => pure (.error reason)
      | .ok (value,next) => set next; pure (.ok value)
    entries := entries.push (⟨definition,parameters,signature,outcome⟩ : MainEntryData)
  let sectionSources := do catalog.array (← supported catalog (← catalog.field source "link_sections" path) path) path
  let sections ← match sectionSources with
    | .error reason => pure (.error reason)
    | .ok records =>
      let mut sections := #[]
      for record in records do
        let name ← catalog.string (← catalog.field record "section" path) path
        let decode : Decode LinkSectionData := do
          let definition ← RegionReader.definition catalog (← catalog.field record "definition" path) path
          let span ← ConstantReader.span catalog (← catalog.field record "span" path) path
          let value ← supported catalog (← catalog.field record "global_query" path) path
          let ty ← typeId catalog typeCount (← catalog.field value "type" path) path
          let allocation ← catalog.natural (← catalog.field (← catalog.field value "allocation" path) "allocation_id" path) path
          unless allocation < allocationCount do throw "link-section static allocation missing from compiler graph"
          return ⟨definition,span,ty,allocation⟩
        let original ← get
        let result ← match decode.run original with
          | .error reason => pure (.error reason)
          | .ok (value,next) => set next; pure (.ok value)
        sections := sections.push (⟨name,result⟩ : LinkSectionQueryData)
      pure (.ok sections)
  return ⟨start,compilerEntry,compilerEntryType,entries,sections⟩

def read (catalog : Catalog) (typeCount allocationCount : Nat) : Decode (Except String MainQueryData) := do
  let original ← get
  match (queries catalog typeCount allocationCount).run original with
  | .error reason => pure (.error reason)
  | .ok (value,next) => set next; pure (.ok value)

end Miri.Input.Reader.MainQueryReader
