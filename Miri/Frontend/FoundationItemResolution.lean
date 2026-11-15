import Miri.Frontend.FoundationGenericEnvironment

namespace Miri.Frontend.Foundation
open Lean

/-- Inherent associated functions are explicit Items, not trait selection.
The retained owner link must agree with the checked lexical impl layer. -/
def sourceInherentItem (document : Document) (definition : Nat) : Except String Bool := do
  let headers ← document.source.getObjValAs? (Array Json) "source_function_signatures"
  let candidates := headers.filter fun h => (h.getObjValAs? Nat "definition").toOption == some definition
  if candidates.isEmpty then return false
  unless candidates.size == 1 do throw "duplicate inherent source header"
  let some header := candidates[0]? | throw "inherent source header absent"
  let owner ← header.getObjVal? "owner_declaration"
  unless (← owner.getObjValAs? String "kind") == "inherent_method" do return false
  let implementation ← owner.getObjValAs? Nat "impl_definition"
  let selfType ← owner.getObjValAs? Nat "self_type"
  let some row := document.definitions[implementation]? | throw "inherent impl source absent"
  unless (← row.getObjValAs? String "kind").startsWith "Impl" do throw "inherent owner is not impl"
  let some methodRow := document.definitions[definition]? | throw "inherent method definition absent"
  let declaration ← methodRow.getObjVal? "generic_declaration"
  unless (← declaration.getObjValAs? Nat "parent") == implementation do throw "inherent method parent mismatch"
  let implDeclaration ← row.getObjVal? "generic_declaration"
  unless (← implDeclaration.getObjValAs? Nat "self_type") == selfType do throw "inherent impl declaration Self mismatch"
  let environment ← header.getObjVal? "environment"
  unless (← environment.getObjValAs? Nat "owner") == definition do throw "inherent method environment owner mismatch"
  let _ ← flattenEnvironment document environment
  let layers ← environment.getObjValAs? (Array Json) "layers"
  let some layer := layers.find? (fun layer => (layer.getObjValAs? Nat "owner").toOption == some implementation)
    | throw "inherent impl lexical layer absent"
  unless (← layer.getObjValAs? Nat "self_type") == selfType do throw "inherent impl Self source mismatch"
  return true


end Miri.Frontend.Foundation
