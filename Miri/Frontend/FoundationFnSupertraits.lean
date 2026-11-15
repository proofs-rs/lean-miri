import Miri.Frontend.FoundationExistentialBounds
import Miri.Frontend.FoundationFnVtable

/-! Declared Fn-family supertrait entailment, with no instance/vtable solver.
The finite declaration graph fixes Self/Args rebasing. Output remains an explicit
existential equality; absence or malformed source is an error, not a guessed
associated-type answer. Auto bounds are preserved exactly, never inferred. -/
namespace Miri.Frontend.Foundation
open Lean

structure SourceFnTraitRef where
  definition : Nat
  arguments : Array ConcreteType

private def sameArgs (a b : Array ConcreteType) : Bool :=
  a.size == b.size && (a.zip b).all (fun (x,y) => sameConcrete 1024 x y)

/-- Derive the finite declared supertrait closure for one instantiated Fn-family
principal. No monomorphic cases are enumerated by the producer. -/
def sourceFnSupertraits (declarations : FnVtableDeclarations) (principal : Nat)
    (arguments : Array ConcreteType) : Except String (Array SourceFnTraitRef) := do
  -- This validates the canonical source headers/signatures, not resolved slots.
  let _ ← fnVtableCandidates declarations principal
  unless arguments.size == 1 do throw "Fn principal argument count mismatch"
  let some (.tuple _) := arguments[0]? | throw "Fn principal Args is not a tuple"
  visit (declarations.declarations.size + 1) #[] #[] principal arguments
where
  visit (fuel : Nat) (active : Array Nat) (seen : Array SourceFnTraitRef)
      (definition : Nat) (arguments : Array ConcreteType) : Except String (Array SourceFnTraitRef) := do
    if active.contains definition then throw "cyclic Fn bound declaration graph"
    if let some previous := seen.find? (·.definition == definition) then
      unless sameArgs previous.arguments arguments do throw "ambiguous Fn supertrait argument rebase"
      return seen
    let .succ fuel := fuel | throw "Fn bound source traversal exhausted"
    let declaration ← fnSourceDeclaration declarations definition
    -- The slot-candidate validator deliberately filters non-trait predicates;
    -- this narrower entailment component requires every captured clause known.
    for clause in (← declaration.getObjValAs? (Array Json) "super_clauses") do
      unless (← clause.getObjValAs? String "kind") == "trait" do
        throw "non-trait Fn declaration clause unsupported"
    let mut seen := seen.push ⟨definition, arguments⟩
    for edge in (← fnSourceSupertraits declarations definition) do
      let target ← fnSourceDeclaration declarations edge.definition
      let kind ← target.getObjValAs? String "lang_item"
      let marker := kind == "meta_sized" || kind == "pointee_sized"
      -- fnVtableCandidates checked the exact index0=Self/index1=Args source
      -- templates on every edge. Markers retain Self and have no extra args.
      let targetArgs := if marker then #[] else arguments
      seen ← visit fuel (active.push definition) seen edge.definition targetArgs
    return seen

private def checkFnObject (document : Document) (declarations : FnVtableDeclarations)
    (source : ExistentialType ConcreteType) (principal : Nat) : Except String (Array SourceFnTraitRef) := do
  unless declarations.definitions == document.definitions do throw "Fn declarations belong to a different source definition world"
  let traits ← sourceFnSupertraits declarations principal source.arguments
  let once ← fnSourceRoot declarations "fn_once"
  let onceDecl ← fnSourceDeclaration declarations once
  let outputs ← (← onceDecl.getObjValAs? (Array Json) "associated_items").filterM fun item => do
    return (← item.getObjValAs? String "kind") == "type" && (← item.getObjValAs? String "name") == "Output"
  unless outputs.size == 1 && source.projections.size == 1 do throw "Fn existential Output equality missing or unsupported"
  let some output := outputs[0]? | throw "FnOnce Output source absent"
  let outputId ← output.getObjValAs? Nat "definition"
  let some projection := source.projections[0]? | throw "Fn existential projection absent"
  let some onceRef := traits.find? (·.definition == once) | throw "FnOnce projection parent not reachable from principal"
  unless projection.definition == outputId && projection.parentTrait == once &&
      sameArgs projection.arguments onceRef.arguments do throw "FnOnce Output source parent/argument mismatch"
  let mut seen := #[]
  for autoTrait in source.autoTraits do
    let some row := document.definitions[autoTrait]? | throw "Fn auto trait source absent"
    unless (← row.getObjValAs? String "kind") == "Trait" &&
        (← row.getObjValAs? Bool "trait_is_auto") && !(seen.contains autoTrait) do
      throw "Fn existential auto trait source inconsistent"
    seen := seen.push autoTrait
  return traits

/-- Check an explicit bound or a declared Fn→FnMut→FnOnce obligation. No other
supertrait/impl search is assumed; a reverse or absent obligation stays an error. -/
def checkSourceExistentialTrait (document : Document) (source : ExistentialType ConcreteType)
    (definition : Nat) (arguments : Array ConcreteType) : Except String Unit := do
  let some principal := source.principal
    | checkExplicitExistentialTrait source definition arguments
  let declarations ← readFnVtableDeclarations document.source
  let roots ← #["fn","fn_mut","fn_once"].mapM (fnSourceRoot declarations)
  unless roots.contains principal do
    checkExplicitExistentialTrait source definition arguments
    return ()
  let traits ← checkFnObject document declarations source principal
  if traits.any (fun reference => reference.definition == definition && sameArgs reference.arguments arguments) then return ()
  checkExplicitExistentialTrait source definition arguments

/-- Validate the Fn hierarchy/Output/auto joins before checking a requested
source projection equality. This still performs no projection normalization. -/
def checkSourceExistentialProjection (document : Document) (source : ExistentialType ConcreteType)
    (definition : Nat) (arguments : Array ConcreteType) (term : ConcreteType) : Except String Unit := do
  let some principal := source.principal | throw "projection has no existential principal"
  let declarations ← readFnVtableDeclarations document.source
  let _ ← checkFnObject document declarations source principal
  checkExplicitExistentialProjection source definition arguments term

end Miri.Frontend.Foundation
