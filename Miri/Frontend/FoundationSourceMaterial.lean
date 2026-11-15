import Miri.Frontend.FoundationSourceConstValues
import Miri.Frontend.FoundationSourceMirUses
import Miri.Frontend.FoundationSourceTraitImpls
import Miri.Frontend.FoundationSourceAllocationIdentity
import Miri.Frontend.FoundationAllocations
import Miri.Frontend.FoundationSourceMir
import Miri.Frontend.FoundationSourceAbi
import Miri.Frontend.FoundationSourceTypes
import Miri.Frontend.FoundationWorldDeclarations
import Miri.Frontend.FoundationTarget
import Miri.Frontend.FoundationForeignDeclarations
import Miri.Frontend.FoundationLinkSections
import Miri.Input.Model.SourceMaterial

/-! One-way decoder projection into the typed evaluation-local carrier. JSON is
used only while parsing, never stored in SourceMaterial or reconstructed by a
runtime query. Unknown typed source constructors remain explicitly unsupported
at demand. No parser object is retained by a runtime compiler query. -/
namespace Miri.Frontend.Foundation
open Lean

private def rawDefinition (document : Document) (id : Nat) : Except String Input.DefinitionId := do
  let some row := document.definitions[id]? | throw "typed source declaration reference absent"
  unless (← row.getObjValAs? Nat "definition_id") == id do throw "typed source declaration reference/index mismatch"
  let crate ← row.getObjValAs? Nat "crate_index"
  let index ← row.getObjValAs? Nat "index"
  unless crate < 2^32 && index < 2^32 do throw "typed source declaration raw DefId exceeds rustc width"
  return ⟨crate,index⟩

private def parseLayer (document : Document) (source : Json) (inherited : Array Input.SourceSymbols.ParameterKind) : Except String Input.SourceMaterial.GenericLayer := do
  let owner ← rawDefinition document (← source.getObjValAs? Nat "owner")
  let parent ← (← source.getObjValAs? (Option Nat) "parent").mapM (rawDefinition document)
  let parameters : Array Input.SourceMaterial.GenericParameter ← (← source.getObjValAs? (Array Json) "parameters").mapM fun parameter => do
    let kind ← match ← parameter.getObjValAs? String "kind" with
      | "type" => pure Input.SourceSymbols.ParameterKind.typeParameter
      | "const" => pure .constParameter
      | "region" => pure .region
      | _ => throw "typed source generic parameter kind unsupported"
    return {
      definition := ← rawDefinition document (← parameter.getObjValAs? Nat "definition")
      index := ← parameter.getObjValAs? Nat "index"
      kind }
  return ⟨owner,parent,← source.getObjValAs? Nat "parent_count",parameters,inherited ++ parameters.map (·.kind)⟩

private def sectionDeclaration (entry : SourceLinkSection) : Except String Input.SourceMaterial.LinkSectionDeclaration := do
  let key ← entry.source.getObjVal? "source_span_key"
  let position ← entry.source.getObjVal? "source_span"
  let start ← position.getObjVal? "start"
  let finish ← position.getObjVal? "end"
  let parentSource ← key.getObjVal? "parent_local_definition"
  let parent : Option Nat ← fromJson? parentSource
  return {
    name := entry.name, definition := ⟨entry.crateIndex,entry.definitionIndex⟩
    span := {
      isDummy := ← position.getObjValAs? Bool "is_dummy"
      lo := ← key.getObjValAs? Nat "lo", hi := ← key.getObjValAs? Nat "hi"
      context := ← key.getObjValAs? String "ctxt", parentLocalDefinition := parent
      file := ← position.getObjValAs? String "file"
      startLine := ← start.getObjValAs? Nat "line", startColumn := ← start.getObjValAs? Nat "column"
      endLine := ← finish.getObjValAs? Nat "line", endColumn := ← finish.getObjValAs? Nat "column" } }

/-- Project only callable declaration capabilities, without letting an unrelated
const/closure body masquerade as a free Item or invalidate known main/start rows.
Every zero-slot Item still retains its original zero-slot source layer. -/
def typedSourceMaterial (document : Document) : Except String Input.SourceMaterial := do
  let mut declarations ← sourceItemDeclarations document
  let headers ← match document.source.getObjVal? "source_function_signatures" with
    | .ok value => fromJson? value
    | .error _ => pure (#[] : Array Json)
  let mut layers : Array Input.SourceMaterial.GenericLayer := #[]
  for row in document.bodies ++ headers do
    let id ← row.getObjValAs? Nat "definition"
    let some definition := document.definitions[id]? | throw "typed source callable owner absent"
    let kind ← definition.getObjValAs? String "kind"
    unless kind == "fn" || kind == "assoc_fn" do continue
    let environment ← row.getObjVal? "environment"
    -- sourceItemDeclarations has checked this callable environment already.
    let mut inherited := #[]
    for original in (← environment.getObjValAs? (Array Json) "layers") do
      let layer ← parseLayer document original inherited
      inherited := layer.flattenedParameters
      if let some old := layers.find? (·.owner == layer.owner) then
        unless old == layer do throw "typed source lexical layer conflict"
      else layers := layers.push layer
  let (foreignItems,foreignLayers) ← ForeignDeclarationSource.itemSource document.source
  for layer in foreignLayers do
    if let some old := layers.find? (·.owner == layer.owner) then
      unless old == layer do throw "foreign/header lexical generic declaration conflict"
    else layers := layers.push layer
  for item in foreignItems do
    if let some old := declarations.find? (·.definition == item.definition) then
      unless old.path == item.path && old.kind == item.kind && old.parameters == item.parameters do
        throw "foreign/header Item declaration conflict"
    else declarations := declarations.push item
  let target : Input.SourceMaterial.Target := {
    triple := document.target.triple
    architecture := document.target.architecture
    dataLayout := document.target.dataLayout
    pointerSizeBits := document.target.pointerSizeBits
    endian := document.target.endian
    runtimeDataLayout := some (← evidenceOfTarget document.target) }
  let linkSections ← (← sourceLinkSections document.source).mapM sectionDeclaration
  let physical ← SourceTypesParser.material document.source
  let constantValues ← SourceConstValuesParser.material document.source physical document.target.pointerSizeBits
  let physical ← SourceConstValuesParser.attachAliasValues physical constantValues
  let material : Input.SourceMaterial := {
    target,declarations,genericLayers := layers,
    genericMir := some (← SourceMirParser.material document (some physical)),
    linkSections := some linkSections,
    allocations := some (← sourceAllocationMaterial document),
    allocationIdentity := ← SourceAllocationIdentityParser.material document.source document.types.size,
    physical := some physical,
    constantValues,
    mirUses := ← SourceMirUsesParser.material document,
    traitImpls := ← SourceTraitImplsParser.material document physical,
    abi := some (← SourceAbiParser.material document)}
  material.validate
  return material

/-- Decoder-only entry for the original finite source text/tree. Its result
contains typed data exclusively; no source JSON survives this boundary. -/
def decodeTypedSourceMaterial (source : Json) : Except String Input.SourceMaterial := do
  typedSourceMaterial (← decode source)

end Miri.Frontend.Foundation
