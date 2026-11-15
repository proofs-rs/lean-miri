import Miri.Frontend.Foundation
import Miri.Input.Model.Catalogs

/-! Pure startup path lookup from finite ordered crates and module children.
Only the fixed core::ascii::escape_default path is supported. Missing graph
nodes are errors, distinct from a complete search finding no matching item. -/
namespace Miri.Frontend.Foundation
open Lean

private def moduleChildren (material : Json) (definition : Nat) : Except String (Array Json) := do
  let modules ← material.getObjValAs? (Array Json) "modules"
  let candidates ← modules.filterM fun node => do
    return (← node.getObjValAs? Nat "definition") == definition
  unless candidates.size == 1 do throw "startup module graph missing/duplicate node"
  let some node := candidates[0]? | throw "startup module absent"
  node.getObjValAs? (Array Json) "children"

/-- Match the pinned Miri helpers::try_resolve_did iteration and namespace
rules. This resolver accepts only the fixed startup path.
It never searches host files or synthesizes a compiler definition identity. -/
def resolveStartupPath (document : Document) (crateName moduleName itemName : String) :
    Except String (Option (Nat × Bool)) := do
  unless crateName == "core" && moduleName == "ascii" && itemName == "escape_default" do
    throw "unsupported startup path demand"
  let material ← document.source.getObjVal? "startup_material"
  unless (← material.getObjValAs? String "capture_scope") == "core_ascii_children" do
    throw "unsupported startup source graph scope"
  unless (← material.getObjValAs? Nat "module_depth") == 1 do
    throw "unsupported startup module graph depth"
  for crate in (← material.getObjValAs? (Array Json) "crates") do
    if (← crate.getObjValAs? String "name") != crateName then continue
    let root ← crate.getObjValAs? Nat "root"
    unless root < document.definitions.size do throw "startup crate root out of bounds"
    let children ← moduleChildren material root
    let modules ← children.filterM fun child => do
      return (← child.getObjValAs? String "name") == moduleName &&
        (← child.getObjValAs? Bool "is_module")
    let some module := modules[0]? | continue
    let some moduleId ← module.getObjValAs? (Option Nat) "definition"
      | throw "startup module child lacks definition"
    unless moduleId < document.definitions.size do throw "startup module identity out of bounds"
    let children ← moduleChildren material moduleId
    for child in children do
      if (← child.getObjValAs? String "name") != itemName then continue
      if (← child.getObjValAs? (Option String) "namespace") != some "value" then continue
      let some id ← child.getObjValAs? (Option Nat) "definition"
        | throw "startup item lacks definition"
      unless id < document.definitions.size do throw "startup definition out of bounds"
      let some available ← child.getObjValAs? (Option Bool) "mir_available"
        | throw "startup value item lacks source MIR availability"
      return some (id, available)
  return none

/-- Build the fixed-interpreter startup preflight facts from source material.
No-core skips lookup exactly as pinned helpers::is_no_core. A missing core path
in an ordinary crate remains Unsupported rather than a successful empty catalog. -/
def startupOfDocument (document : Document) : Except String Input.Catalog.Startup := do
  let material ← document.source.getObjVal? "startup_material"
  let noCore ← material.getObjValAs? Bool "no_core"
  if noCore then return ⟨true, none⟩
  let some resolved ← resolveStartupPath document "core" "ascii" "escape_default"
    | throw "startup source graph does not resolve core::ascii::escape_default"
  return ⟨false, some resolved⟩

end Miri.Frontend.Foundation
