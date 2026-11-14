import Miri.Input.TraitSelection.Material

namespace Miri.Input.TraitSelection.RelevantImpl
open GenericSubstitution

/-! Pinned rustc `ty/trait_def.rs::for_each_relevant_impl` and
`rustc_type_ir/fast_reject.rs::simplify_type`. This is a source-head lookup key,
not unification or fulfillment. A possibly relevant auto impl disqualifies the
structural candidate even when its argument relation or where clauses fail. -/
inductive Key where
  | scalar (kind payload : String)
  | adt (definition : DefinitionIdentity)
  | foreign (definition : DefinitionIdentity)
  | closure (definition : DefinitionIdentity)
  | coroutine (definition : DefinitionIdentity)
  | coroutineWitness (definition : DefinitionIdentity)
  | tuple (length : Nat)
  | function (arity : Nat)
  | pointer (mutability : String)
  | reference (mutability : String)
  | array | slice | string | never | unsafeBinder | placeholder
  deriving Repr, DecidableEq

private def length : Terms → Nat
  | .nil => 0
  | .cons _ tail => length tail + 1

private def functionArity : Term → Except String Nat
  | .binder _ (.node .aggregate "signature" _ types) =>
    if length types > 0 then .ok (length types - 1)
    else .error "source function signature has no return type"
  | _ => .error "source function signature representation unsupported"

/-- `instantiate=true` is rustc TreatParams::InstantiateWithInfer for impl
headers. Query goals use false after normalization/groundness validation. -/
def simplify (instantiate : Bool) : Nat → Term → Except String (Option Key)
  | 0, _ => .error "source impl relevance simplification exhausted"
  | fuel + 1, term => do
    match term with
    | .parameter .type _ => pure (if instantiate then none else some .placeholder)
    | .placeholder .type .. => pure (some .placeholder)
    | .definition .type tag definition _ =>
      if tag.startsWith "alias_" then return if instantiate then none else some .placeholder
      match tag with
      | "adt" => pure (some (.adt definition))
      | "foreign" => pure (some (.foreign definition))
      | "function_definition" | "closure" | "coroutine_closure" => pure (some (.closure definition))
      | "coroutine" => pure (some (.coroutine definition))
      | "coroutine_witness" => pure (some (.coroutineWitness definition))
      | _ => throw "unknown source definition shape in impl relevance"
    | .atom .type tag payload =>
      match tag with
      | "bool" | "char" | "int" | "uint" | "float" => pure (some (.scalar tag payload))
      | "str" => pure (some .string)
      | "never" => pure (some .never)
      | _ => throw "unknown source atom shape in impl relevance"
    | .node .type tag payload children =>
      match tag, children with
      | "pattern", .cons inner (.cons _ .nil) => simplify instantiate fuel inner
      | "tuple", children => pure (some (.tuple (length children)))
      | "array", .cons _ (.cons _ .nil) => pure (some .array)
      | "slice", .cons _ .nil => pure (some .slice)
      | "raw_pointer", .cons _ .nil =>
        unless payload == "mutable" || payload == "immutable" do throw "invalid raw pointer mutability"
        pure (some (.pointer payload))
      | "reference", .cons _ (.cons _ .nil) =>
        unless payload == "mutable" || payload == "immutable" do throw "invalid reference mutability"
        pure (some (.reference payload))
      | "function_pointer", .cons signature .nil => pure (some (.function (← functionArity signature)))
      | "unsafe_binder", .cons _ .nil => pure (some .unsafeBinder)
      | "dynamic", _ => throw "dynamic impl relevance requires principal trait classification"
      | _, _ => throw "unknown or malformed source structural shape in impl relevance"
    | .bound .. | .inference .. =>
      if instantiate then pure none else throw "impl relevance requires a rigid query Self"
    | _ => throw "impl relevance requires a type Self"

/-- All currently represented concrete fast-reject keys are distinct from
rustc Trait/MarkerTraitObject keys. This proves only head disjointness: a
blanket/alias head remains possible, while Dynamic or unknown syntax errors.
Declaration identity and generic/header validation remain caller checks. -/
def dynamicHeadPossible (fuel : Nat) (source : Term) : Except String Bool := do
  let key ← simplify true fuel source
  pure key.isNone

def possible (fuel : Nat) (implementation : Impl) (goal : TraitRef) : Except String Bool := do
  if implementation.traitRef.definition != goal.definition then return false
  let some source := implementation.traitRef.arguments[0]? | throw "source impl Self absent"
  let some target := goal.arguments[0]? | throw "query Self absent"
  let some sourceKey ← simplify true fuel source | return true
  let some targetKey ← simplify false fuel target | throw "rigid query Self has no simplified type"
  -- for_each_relevant_impl deliberately visits no nonblanket witness impls.
  if let .coroutineWitness _ := targetKey then return false
  pure (decide (sourceKey = targetKey))

end Miri.Input.TraitSelection.RelevantImpl
