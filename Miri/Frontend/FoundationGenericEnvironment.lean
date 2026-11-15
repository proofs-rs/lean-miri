import Miri.Frontend.Foundation

/-! Uniform declaration layers, flattened only by checked pure Lean traversal.
Lexical inheritance is distinct from an impl's self-type source link. No missing
arguments, predicates or defaults are supplied by this operation. -/
namespace Miri.Frontend.Foundation
open Lean

private def requiredOptionalNat (source : Json) (key : String) : Except String (Option Nat) := do
  let value ← source.getObjVal? key
  fromJson? value

/-- Derive the ordered parameter/predicate view. Every owner and original
parameter index is checked against its captured declaration identity. -/
def flattenEnvironment (document : Document) (source : Json) : Except String Json := do
  let owner ← source.getObjValAs? Nat "owner"
  let layers ← source.getObjValAs? (Array Json) "layers"
  unless !layers.isEmpty do throw "generic source layers absent"
  let mut parameters : Array Json := #[]
  let mut clauses : Array Json := #[]
  let mut previous : Option Nat := none
  let mut seen : Array Nat := #[]
  for layer in layers do
    let definition ← layer.getObjValAs? Nat "owner"
    unless !seen.contains definition do throw "generic source owner cycle/duplicate"
    let some row := document.definitions[definition]? | throw "generic source owner absent"
    unless (← row.getObjValAs? Nat "definition_id") == definition do throw "generic source owner identity mismatch"
    let declaration ← row.getObjVal? "generic_declaration"
    let ownerKind ← row.getObjValAs? String "kind"
    let hasSelf ← layer.getObjValAs? Bool "has_self"
    unless hasSelf == (← declaration.getObjValAs? Bool "has_self") do
      throw "generic declaration/layer Self witness mismatch"
    let parent ← requiredOptionalNat layer "parent"
    unless parent == previous && parent == (← requiredOptionalNat declaration "parent") do
      throw "generic source lexical parent mismatch"
    let parentCount ← layer.getObjValAs? Nat "parent_count"
    unless parentCount == parameters.size && parentCount == (← declaration.getObjValAs? Nat "parent_count") do
      throw "generic source inherited count mismatch"
    let selfType ← requiredOptionalNat layer "self_type"
    unless selfType == (← requiredOptionalNat declaration "self_type") do throw "generic impl self-type link mismatch"
    if let some type := selfType then
      unless type < document.types.size do throw "generic impl self-type source absent"
      unless (← row.getObjValAs? String "kind").startsWith "Impl" do throw "self-type link on non-impl owner"
    else
      if (← row.getObjValAs? String "kind").startsWith "Impl" then throw "generic impl self-type link missing"
    let own ← layer.getObjValAs? (Array Json) "parameters"
    unless own.size == (← declaration.getObjValAs? Nat "own_parameter_count") do throw "generic own parameter count mismatch"
    for index in [:own.size] do
      let some parameter := own[index]? | throw "generic source parameter absent"
      let expectedIndex := parentCount + index
      unless (← parameter.getObjValAs? Nat "index") == expectedIndex do throw "generic source parameter order/index mismatch"
      let id ← parameter.getObjValAs? Nat "definition"
      let some row := document.definitions[id]? | throw "generic parameter declaration absent"
      let kind ← parameter.getObjValAs? String "kind"
      let expectedKind ← match kind with
        | "type" => pure "TyParam"
        | "const" => pure "ConstParam"
        | "region" => pure "LifetimeParam"
        | _ => throw "generic parameter kind unsupported"
      let actualKind ← row.getObjValAs? String "kind"
      -- Pinned generics_of.rs:242–252 reuses the trait owner DefId
      -- for the implicit Self type parameter; it is not a synthetic TyParam.
      let implicitSelf := kind == "type" && ownerKind == "Trait" &&
        id == definition && expectedIndex == 0 && parentCount == 0 && hasSelf
      if implicitSelf then
        unless !(← parameter.getObjValAs? Bool "has_default") &&
            (← parameter.getObjVal? "default") == Json.null do
          throw "implicit trait Self has a default"
      unless (← row.getObjValAs? Nat "definition_id") == id &&
          (actualKind == expectedKind || (implicitSelf && actualKind == ownerKind)) do
        throw "generic parameter identity/kind mismatch"
      let identity ← row.getObjVal? "generic_parameter"
      unless (← identity.getObjValAs? Nat "owner") == definition &&
          (← identity.getObjValAs? Nat "index") == expectedIndex do throw "generic parameter owner/index mismatch"
    parameters := parameters ++ own
    clauses := clauses ++ (← layer.getObjValAs? (Array Json) "clauses")
    seen := seen.push definition
    previous := some definition
  unless previous == some owner do throw "generic environment terminal owner mismatch"
  return Json.mkObj [("parameters",toJson parameters),("clauses",toJson clauses)]

end Miri.Frontend.Foundation
