import Miri.Frontend.FoundationGenericEnvironment

/-! A deliberately small declaration-header matcher. All impl headers are
examined; rigid ADT/never heads cannot unify with unit, while unknown roots,
conditional matching headers, negative impls and ambiguity fail closed.
No compiler trait selection or method instance is embedded in source data. -/
namespace Miri.Frontend.Foundation
open Lean

structure SourceUnitTraitSelection where
  traitDefinition : Nat
  implementationDefinition : Nat
  traitMethodDefinition : Nat
  implementationMethodDefinition : Nat
  arguments : Array ConcreteType := #[]

private def sourceDefinition (document : Document) (id : Nat) (kind : String) : Except String Unit := do
  let some row := document.definitions[id]? | throw "trait declaration identity absent"
  unless (← row.getObjValAs? Nat "definition_id") == id &&
      (← row.getObjValAs? String "kind").startsWith kind do throw "trait declaration identity/kind mismatch"

/-- Select an unambiguous unconditional unit impl of the demanded language
trait, and its sole declaration-linked method. Names and numeric IDs play no
role in matching; method instance/shim construction remains a separate query. -/
def sourceTerminationUnitSelection (document : Document) (traitDefinition : Nat)
    (self : ConcreteType) : Except String SourceUnitTraitSelection := do
  match self with
  | .tuple fields => unless fields.isEmpty do throw "termination matcher currently supports unit Self only"
  | _ => throw "termination matcher currently supports unit Self only"
  let source ← document.source.getObjVal? "termination_source"
  unless (← source.getObjValAs? String "lang_item") == "termination" &&
      (← source.getObjValAs? Nat "definition") == traitDefinition &&
      (← source.getObjValAs? Bool "complete_impl_headers") do throw "missing demanded complete termination headers"
  sourceDefinition document traitDefinition "Trait"
  unless !(← source.getObjValAs? Bool "auto") && !(← source.getObjValAs? Bool "marker") &&
      !(← source.getObjValAs? Bool "coinductive") && (← source.getObjValAs? String "safety") == "Safe" &&
      (← source.getObjValAs? String "constness") == "NotConst" do throw "unsupported termination trait declaration"
  unless (← source.getObjValAs? Nat "parameter_count") == 1 &&
      (← source.getObjValAs? Bool "has_self") &&
      (← source.getObjValAs? (Option Nat) "generic_parent").isNone do throw "termination trait generic parameters unsupported"
  let metaSized ← source.getObjValAs? Nat "meta_sized_definition"
  for clause in (← source.getObjValAs? (Array Json) "super_clauses") do
    unless (← clause.getObjValAs? String "kind") == "trait" &&
        (← clause.getObjValAs? Nat "definition") == metaSized &&
        (← clause.getObjValAs? String "polarity") == "Positive" &&
        (← clause.getObjValAs? Nat "argument_count") == 1 &&
        (← clause.getObjValAs? Nat "self_parameter") == 0 &&
        (← clause.getObjValAs? Nat "bound_variable_count") == 0 do throw "unsupported termination super obligation"
  let methods ← source.getObjValAs? (Array Json) "associated_items"
  unless methods.size == 1 do throw "termination method declaration domain unsupported"
  let some method := methods[0]? | throw "termination method absent"
  unless (← method.getObjValAs? String "kind") == "method" &&
      (← method.getObjValAs? Bool "has_self") &&
      (← method.getObjValAs? Nat "own_parameter_count") == 0 do throw "termination associated declaration unsupported"
  let traitMethod ← method.getObjValAs? Nat "definition"
  sourceDefinition document traitMethod "assoc_fn"
  let mut seen : Array Nat := #[]
  let mut selected : Option SourceUnitTraitSelection := none
  for header in (← source.getObjValAs? (Array Json) "implementations") do
    let implementation ← header.getObjValAs? Nat "definition"
    unless !seen.contains implementation do throw "duplicate termination impl header"
    seen := seen.push implementation
    sourceDefinition document implementation "Impl"
    unless (← header.getObjValAs? Nat "trait_definition") == traitDefinition &&
        (← header.getObjValAs? Nat "argument_count") == 1 do throw "termination impl trait identity mismatch"
    let head ← header.getObjVal? "self_constructor"
    let applies ← match ← head.getObjValAs? String "kind" with
      | "adt" | "never" => pure false
      | "tuple" => pure ((← head.getObjValAs? Nat "arity") == 0)
      | _ => throw "termination impl head may overlap unit; unsupported"
    if applies then
      unless (← header.getObjValAs? Nat "parameter_count") == 0 &&
          (← header.getObjValAs? Nat "clause_count") == 0 &&
          (← header.getObjValAs? (Option Nat) "generic_parent").isNone &&
          (← header.getObjValAs? (Option Nat) "clause_parent").isNone &&
          (← header.getObjValAs? String "polarity") == "Positive" &&
          (← header.getObjValAs? String "constness") == "NotConst" &&
          (← header.getObjValAs? Bool "final") do throw "conditional/negative/specializable unit impl unsupported"
      let items ← header.getObjValAs? (Array Json) "associated_items"
      unless items.size == 1 do throw "unit impl method count unsupported"
      let some item := items[0]? | throw "unit impl method absent"
      unless (← item.getObjValAs? String "kind") == "method" &&
          (← item.getObjValAs? Nat "trait_item") == traitMethod &&
          (← item.getObjValAs? Nat "own_parameter_count") == 0 do throw "unit impl method declaration link mismatch"
      let implMethod ← item.getObjValAs? Nat "definition"
      sourceDefinition document implMethod "assoc_fn"
      unless selected.isNone do throw "ambiguous termination unit impl headers"
      selected := some ⟨traitDefinition,implementation,traitMethod,implMethod,#[]⟩
  let some result := selected | throw "no supported termination unit impl"
  return result

end Miri.Frontend.Foundation
