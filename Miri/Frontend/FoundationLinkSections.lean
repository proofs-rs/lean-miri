import Lean
import Miri.Input.Model.Catalogs

/-! Finite source selection matching pinned helpers.rs::iter_exported_symbols
and lookup_link_section. An executable dependency format is mandatory even for
an empty answer; nonempty sections still need genuine global initializer and
allocation identity material, which this adapter does not construct. -/
namespace Miri.Frontend.Foundation
open Lean

structure SourceLinkSection where
  name : String
  crateIndex : Nat
  definitionIndex : Nat
  source : Json

private def appendSection (selected : Array SourceLinkSection) (item : Json) (used : Bool) :
    Except String (Array SourceLinkSection) := do
  let name ← item.getObjValAs? (Option String) "link_section"
  let crateIndex ← item.getObjValAs? Nat "crate_index"
  let definitionIndex ← item.getObjValAs? Nat "definition_index"
  let _ ← item.getObjValAs? String "definition_kind"
  let span ← item.getObjVal? "source_span_key"
  let lo ← span.getObjValAs? Nat "lo"
  let hi ← span.getObjValAs? Nat "hi"
  unless lo ≤ hi do throw "reversed link-section source span"
  let _ ← span.getObjValAs? String "ctxt"
  let _ ← span.getObjValAs? (Option Nat) "parent_local_definition"
  if used then
    if let some name := name then return selected.push ⟨name,crateIndex,definitionIndex,item⟩
  return selected

/-- Select in source traversal order. Linkage and export lists are retained
inputs, not a boolean completeness assertion or an invented empty default. -/
def sourceLinkSections (document : Json) : Except String (Array SourceLinkSection) := do
  let material ← document.getObjVal? "link_section_material"
  let localCrate ← material.getObjValAs? Nat "local_crate"
  unless localCrate == 0 do throw "source local crate identity differs from pinned LOCAL_CRATE"
  let locals ← material.getObjValAs? (Array Json) "local_items"
  let mut selected := #[]
  for item in locals do
    unless (← item.getObjValAs? Nat "crate_index") == localCrate do
      throw "local link-section source belongs to another crate"
    let used := (← item.getObjValAs? Bool "used_compiler") || (← item.getObjValAs? Bool "used_linker")
    let external ← item.getObjValAs? Bool "extern_indicator"
    if used || external then selected ← appendSection selected item used
  let some dependencies ← material.getObjValAs? (Option (Array Json)) "executable_dependencies"
    | throw "link sections require executable dependency format source"
  for h : i in [:dependencies.size] do
    let dependency := dependencies[i]
    unless (← dependency.getObjValAs? Nat "crate_index") == i do
      throw "dependency format crate indices must be dense"
    let linkage ← dependency.getObjValAs? String "linkage"
    unless #["NotLinked","IncludedFromDylib","Static","Dynamic"].contains linkage do
      throw "unknown executable dependency linkage"
    let exports ← dependency.getObjValAs? (Array Json) "exports"
    if i == localCrate || linkage == "NotLinked" then
      unless exports.isEmpty do throw "untraversed dependency has export source rows"
    else
      for symbol in exports do
        match ← symbol.getObjValAs? String "kind" with
        | "other" => pure ()
        | "non_generic" =>
          let used ← symbol.getObjValAs? Bool "used"
          unless (← symbol.getObjValAs? Bool "is_foreign") do
            selected ← appendSection selected (← symbol.getObjVal? "item") used
        | _ => throw "unknown exported symbol source kind"
  return selected

/-- Genuine empty source selection can populate Main.linkSections. A selected
static needs its actual initializer/type/allocation graph; none is synthesized. -/
def checkedEmptyLinkSections (document : Json) : Except String (Array Input.Catalog.LinkSection) := do
  unless (← sourceLinkSections document).isEmpty do
    throw "selected link section requires source global initializer and allocation identity"
  return #[]

end Miri.Frontend.Foundation
