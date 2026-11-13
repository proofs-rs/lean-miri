import Miri.Input.GenericSubstitution

/-! Lossless existential-predicate syntax shared by material and constructed
trait objects. Physical definitions and child IDs are source identities;
projection terms retain their Type/Const distinction. No vtable or normalized
predicate answer enters these records. -/
namespace Miri.Input.DynamicPredicate
open GenericSubstitution

inductive ProjectionTerm where
  | type (id : MIR.TyId)
  | constant (id : MIR.TypeConstId)
  deriving Repr, DecidableEq, BEq

inductive Body where
  | trait (definition : DefinitionIdentity) (arguments : Array MIR.GenericArg)
  | projection (definition : DefinitionIdentity) (arguments : Array MIR.GenericArg) (term : ProjectionTerm)
  | autoTrait (definition : DefinitionIdentity)
  deriving Repr, DecidableEq

structure Predicate where
  variables : Array BoundVariable
  body : Body
  deriving Repr, DecidableEq

structure Dynamic where
  predicates : Array Predicate
  region : MIR.Region
  deriving Repr, DecidableEq

def Body.definition : Body → DefinitionIdentity
  | .trait definition _ | .projection definition .. | .autoTrait definition => definition

def Body.rank : Body → Nat
  | .trait .. => 0 | .projection .. => 1 | .autoTrait .. => 2

def Body.arguments : Body → Array MIR.GenericArg
  | .trait _ arguments | .projection _ arguments _ => arguments
  | .autoTrait _ => #[]

def Body.typeChildren (body : Body) : Array MIR.TyId :=
  let arguments := body.arguments.filterMap fun value => match value with | .Type id => some id | _ => none
  match body with | .projection _ _ (.type id) => arguments.push id | _ => arguments

def Body.constantChildren (body : Body) : Array MIR.TypeConstId :=
  let arguments := body.arguments.filterMap fun value => match value with | .Const id => some id | _ => none
  match body with | .projection _ _ (.constant id) => arguments.push id | _ => arguments

private def arrayOfTerms (result : Array Term) : Terms → Array Term
  | .nil => result | .cons head tail => arrayOfTerms (result.push head) tail

/-- Read the complete binder and body; the callback resolves child source terms
in the caller's execution universe. A projection cannot contain a lifetime. -/
def read [Monad m] [MonadExceptOf String m] (argument : Term → m MIR.GenericArg)
    (term : Term) : m Predicate := do
  let .binder variables body := term | throw "existential predicate requires its raw binder"
  let body ← match body with
    | .definition .aggregate "trait" definition children =>
      pure (Body.trait definition (← (arrayOfTerms #[] children).mapM argument))
    | .definition .aggregate "auto_trait" definition .nil => pure (Body.autoTrait definition)
    | .definition .aggregate "projection" definition children =>
      let children := arrayOfTerms #[] children
      let some term := children.back? | throw "existential projection term is absent"
      let projected ← match ← argument term with
        | .Type id => pure (ProjectionTerm.type id)
        | .Const id => pure (ProjectionTerm.constant id)
        | .Lifetime _ => throw "existential projection term is a lifetime"
      pure (Body.projection definition (← children.pop.mapM argument) projected)
    | _ => throw "existential predicate body is not a raw trait, projection or auto trait"
  pure ⟨variables,body⟩

def write [Monad m] (argument : MIR.GenericArg → m Term) (predicate : Predicate) : m Term := do
  let body ← match predicate.body with
    | .trait definition arguments =>
      pure (.definition .aggregate "trait" definition (Terms.ofArray (← arguments.mapM argument)))
    | .autoTrait definition => pure (.definition .aggregate "auto_trait" definition .nil)
    | .projection definition arguments projected =>
      let arguments ← arguments.mapM argument
      let projected ← argument (match projected with | .type id => .Type id | .constant id => .Const id)
      pure (.definition .aggregate "projection" definition (Terms.ofArray (arguments.push projected)))
  pure (.binder predicate.variables body)

def readDynamic [Monad m] [MonadExceptOf String m] (argument : Term → m MIR.GenericArg)
    (region : Term → m MIR.Region) (term : Term) : m Dynamic := do
  let .node .type "dynamic" "" children := term | throw "trait object requires its raw dynamic constructor"
  let children := arrayOfTerms #[] children
  let some lifetime := children.back? | throw "trait object source lifetime is absent"
  unless !children.pop.isEmpty do throw "trait object source predicate list is empty"
  pure ⟨← children.pop.mapM (read argument), ← region lifetime⟩

def writeDynamic [Monad m] (argument : MIR.GenericArg → m Term)
    (region : MIR.Region → m Term) (value : Dynamic) : m Term := do
  let predicates ← value.predicates.mapM (write argument)
  pure (.node .type "dynamic" "" (Terms.ofArray (predicates.push (← region value.region))))
end Miri.Input.DynamicPredicate
