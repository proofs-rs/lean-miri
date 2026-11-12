import Miri.Input.TraitSelection.Material

/-! Impl-head matching for ground trait queries. Pinned rustc
8144389c895da997dbdecaa635e41d6a50be6ffd, impl candidate matching creates fresh
impl variables and relates the instantiated trait ref to the query. Here the
impl parameters are the only assignable variables; query inference is rejected
rather than treated as a mismatch. Repeated parameters must agree, and type,
region and const sorts are preserved. Alias normalization is an explicit caller
operation. Unsupported higher-ranked relations remain errors. -/
namespace Miri.Input.TraitSelection.Match
open GenericSubstitution

/-- Filtering a concrete root-Self constructor is complete only for queries
whose full normalized type graph stays in the declared source constructor set. -/
def requireConstructorScope (allowed : Array DefinitionIdentity) : Nat → Term → Except String Unit
  | 0, _ => .error "trait constructor scope traversal exhausted"
  | fuel + 1, term => do
    match term with
    | .definition sort tag definition children =>
      if sort == .type && tag == "adt" && !allowed.contains definition then
        throw "trait query ADT constructor outside closed source declaration scope"
      let _ ← children.mapM fun child => do
        requireConstructorScope allowed fuel child
        pure child
    | .node _ _ _ children =>
      let _ ← children.mapM fun child => do
        requireConstructorScope allowed fuel child
        pure child
    | .binder _ body => requireConstructorScope allowed fuel body
    | _ => pure ()

abbrev Bindings := Array (Option Term)

private def closed : Nat → Nat → Term → Except String Bool
  | 0, _, _ => .error "trait matching variable traversal exhausted"
  | fuel + 1, depth, term => do
    match term with
    | .parameter .. | .inference .. => pure false
    | .node sort tag _ children =>
      if sort == .constant && tag != "value" then
        throw "trait matching requires evaluated constants"
      return !(← children.anyM fun child => return !(← closed fuel depth child))
    | .definition _ tag _ children =>
      if tag.startsWith "alias_" then throw "trait matching requires normalized aliases"
      return !(← children.anyM fun child => return !(← closed fuel depth child))
    | .binder variables body =>
      if variables.isEmpty && body.sort == .aggregate then closed fuel depth body
      else pure false
    | .bound _ (.Bound index) _ _ => pure (index < depth)
    | .bound _ .Canonical _ _ | .placeholder .. => pure false
    | _ => pure true

mutual
private def terms (parameters : Array ArgSort) (eraseRegions : Bool) : Nat → Terms → Terms → Bindings →
    Except String (Option Bindings)
  | 0, _, _, _ => .error "trait impl-head matching exhausted"
  | _ + 1, .nil, .nil, bindings => pure (some bindings)
  | fuel + 1, .cons p ps, .cons q qs, bindings => do
    let some bindings ← term parameters eraseRegions fuel p q bindings | return none
    terms parameters eraseRegions fuel ps qs bindings
  | _ + 1, _, _, _ => pure none

private def term (parameters : Array ArgSort) (eraseRegions : Bool) : Nat → Term → Term → Bindings →
    Except String (Option Bindings)
  | 0, _, _, _ => .error "trait impl-head matching exhausted"
  | fuel + 1, pattern, goal, bindings => do
    unless ← closed (fuel + 1) 0 goal do throw "trait matching requires a ground query"
    unless pattern.sort == goal.sort do return none
    if eraseRegions && pattern.sort == .region then
      match pattern with
      | .parameter .. => pure ()
      | .inference .. => throw "inference variable in raw impl declaration"
      | _ => return some bindings
    match pattern with
    | .parameter sort index =>
      let some expected := parameters[index]? | throw "impl parameter index out of bounds"
      unless sort == expected do throw "impl parameter sort disagrees with declaration"
      let some binding := bindings[index]? | throw "impl binding slot absent"
      let goal := if eraseRegions && sort == .region then .atom .region "erased" "" else goal
      match binding with
      | some prior => pure (if prior = goal then some bindings else none)
      | none =>
        if bound : index < bindings.size then
          pure (some (bindings.set index (some goal) bound))
        else throw "impl binding index out of bounds"
    | .inference .. => throw "inference variable in raw impl declaration"
    | .atom sort tag payload =>
      match goal with
      | .atom otherSort otherTag otherPayload =>
        pure (if sort == otherSort && tag == otherTag && payload == otherPayload then some bindings else none)
      | _ => pure none
    | .node sort tag payload children =>
      if sort == .constant && tag != "value" then
        throw "impl const expression requires deferred evaluation"
      match goal with
      | .node otherSort otherTag otherPayload otherChildren =>
        if sort != otherSort || tag != otherTag || payload != otherPayload then return none
        terms parameters eraseRegions fuel children otherChildren bindings
      | _ => pure none
    | .definition sort tag identity children =>
      if tag.startsWith "alias_" then throw "impl projection requires deferred normalization"
      match goal with
      | .definition otherSort otherTag otherIdentity otherChildren =>
        if sort != otherSort || tag != otherTag || identity != otherIdentity then return none
        terms parameters eraseRegions fuel children otherChildren bindings
      | _ => pure none
    | .binder variables body =>
      unless variables.isEmpty && body.sort == .aggregate do
        throw "higher-ranked impl-head relation requires universe checking"
      match goal with
      | .binder otherVariables otherBody =>
        unless otherVariables.isEmpty && otherBody.sort == .aggregate do
          throw "higher-ranked impl-head relation requires universe checking"
        term parameters eraseRegions fuel body otherBody bindings
      | _ => pure none
    | .bound .. | .placeholder .. =>
      throw "higher-ranked impl-head relation requires universe checking"
end

/-- Required before candidate enumeration, including an empty impl catalog. -/
def requireGround (fuel : Nat) (value : Term) : Except String Unit := do
  unless ← closed fuel 0 value do throw "trait matching requires a ground query"

/-- A missing binding is not filled with an invented type. Region erasure may
supply erased regions only when explicitly authorized by the query environment. -/
def complete (parameters : Array ArgSort) (eraseRegions : Bool) (bindings : Bindings) :
    Except String (Array Term) := do
  unless parameters.size == bindings.size do throw "impl binding arity mismatch"
  let mut arguments := #[]
  for index in [:parameters.size] do
    let some sort := parameters[index]? | throw "impl parameter absent"
    let some binding := bindings[index]? | throw "impl binding slot absent"
    let argument ← match binding with
      | some value => pure value
      | none =>
        if eraseRegions && sort == .region then pure (.atom .region "erased" "")
        else throw "impl parameter remains unconstrained"
    unless argument.sort == sort do throw "impl substitution sort mismatch"
    arguments := arguments.push argument
  pure arguments

def head (fuel : Nat) (implementation : Impl) (goal : TraitRef) (eraseRegions : Bool := false) :
    Except String (Option Bindings) := do
  if implementation.traitRef.definition != goal.definition then return none
  terms implementation.parameters eraseRegions fuel
    (Terms.ofArray implementation.traitRef.arguments) (Terms.ofArray goal.arguments)
    (Array.replicate implementation.parameters.size none)

end Miri.Input.TraitSelection.Match
