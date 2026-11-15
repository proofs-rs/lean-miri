import Lean

/-! Structural existential syntax only. Definition identities remain local to
one finite document; no trait normalization, selection, layout or vtable lookup
is inferred from a parsed projection equality. -/
namespace Miri.Frontend.Foundation
open Lean

structure ExistentialProjection (α : Type) where
  definition : Nat
  parentTrait : Nat
  arguments : Array α
  term : α
  deriving Repr

structure ExistentialType (α : Type) where
  region : String
  principal : Option Nat
  arguments : Array α
  projections : Array (ExistentialProjection α)
  autoTraits : Array Nat
  deriving Repr

def mapExistentialM (f : α → Except String β) (source : ExistentialType α) :
    Except String (ExistentialType β) := do
  let arguments ← source.arguments.mapM f
  let projections ← source.projections.mapM fun projection => do
    let arguments ← projection.arguments.mapM f
    let term ← f projection.term
    return (⟨projection.definition, projection.parentTrait, arguments, term⟩ : ExistentialProjection β)
  return ⟨source.region, source.principal, arguments, projections, source.autoTraits⟩

def sameExistential (equal : α → α → Bool) (a b : ExistentialType α) : Bool :=
  a.region == b.region && a.principal == b.principal && a.autoTraits == b.autoTraits &&
    a.arguments.size == b.arguments.size && (a.arguments.zip b.arguments).all (fun (x,y) => equal x y) &&
    a.projections.size == b.projections.size && (a.projections.zip b.projections).all (fun (x,y) =>
      x.definition == y.definition && x.parentTrait == y.parentTrait && equal x.term y.term &&
      x.arguments.size == y.arguments.size && (x.arguments.zip y.arguments).all (fun (u,v) => equal u v))

private def checkDefinition (definitions : Array Json) (id : Nat) (kind : String) : Except String Json := do
  let some row := definitions[id]? | throw "existential definition absent"
  unless (← row.getObjValAs? String "kind") == kind do throw "existential definition category mismatch"
  return row

private def readArguments (readType : Nat → Except String α) (source : Json) : Except String (Array α) := do
  (← source.getObjValAs? (Array Json) "arguments").mapM fun argument => do
    unless (← argument.getObjValAs? String "kind") == "type" do
      throw "non-type existential argument unsupported"
    readType (← argument.getObjValAs? Nat "type")

/-- Preserve principal/projection/auto predicate order and source identities.
Only binder-free type-valued projections and type arguments are understood. -/
def parseExistential (definitions : Array Json) (readType : Nat → Except String α)
    (source : Json) : Except String (ExistentialType α) := do
  let region ← source.getObjValAs? String "region"
  unless region == "erased" || region == "static" do throw "unsupported existential region"
  let mut principal := none
  let mut arguments := #[]
  let mut projections : Array (ExistentialProjection α) := #[]
  let mut autoTraits : Array Nat := #[]
  for predicate in (← source.getObjValAs? (Array Json) "predicates") do
    unless (← predicate.getObjValAs? (Array Json) "bound_variables").isEmpty do
      throw "bound existential predicates unsupported"
    let definition ← predicate.getObjValAs? Nat "definition"
    match ← predicate.getObjValAs? String "kind" with
    | "trait" =>
      unless principal.isNone && projections.isEmpty && autoTraits.isEmpty do throw "duplicate/out-of-order existential principal"
      let row ← checkDefinition definitions definition "Trait"
      unless !(← row.getObjValAs? Bool "trait_is_auto") do throw "auto trait used as existential principal"
      principal := some definition
      arguments ← readArguments readType predicate
    | "auto_trait" =>
      let row ← checkDefinition definitions definition "Trait"
      unless (← row.getObjValAs? Bool "trait_is_auto") && !(autoTraits.contains definition) do
        throw "invalid/duplicate existential auto trait"
      autoTraits := autoTraits.push definition
    | "projection" =>
      unless principal.isSome && autoTraits.isEmpty do throw "projection without principal or after auto traits"
      let _ ← checkDefinition definitions definition "AssocTy"
      let parentTrait ← predicate.getObjValAs? Nat "parent_trait"
      let _ ← checkDefinition definitions parentTrait "Trait"
      unless !(projections.any (·.definition == definition)) do throw "duplicate existential projection"
      let term ← predicate.getObjVal? "term"
      unless (← term.getObjValAs? String "kind") == "type" do throw "non-type existential projection unsupported"
      let projectedArguments ← readArguments readType predicate
      let term ← readType (← term.getObjValAs? Nat "type")
      projections := projections.push ⟨definition, parentTrait, projectedArguments, term⟩
    | _ => throw "unsupported existential predicate kind"
  return ⟨region, principal, arguments, projections, autoTraits⟩

end Miri.Frontend.Foundation
