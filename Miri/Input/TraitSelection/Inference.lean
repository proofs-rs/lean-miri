import Miri.Input.TraitSelection.Universes
import Miri.Input.TraitSelection.RegionLeakCheck

/-! Query-local equality inference. Variables have explicit sort and creation
universe; assignments are resolved transitively and cannot capture a placeholder
from a universe that an earlier variable cannot name. Region constraints retain
their direction and are checked after assignment resolution. This is substrate
for quantified relations, not an independent successful trait-query provider. -/
namespace Miri.Input.TraitSelection.Inference
open GenericSubstitution

structure Variable where
  sort : ArgSort
  createdIn : Nat
  assignment : Option Term := none
  deriving Repr, DecidableEq

structure State where
  lastUniverse : Nat := 0
  variables : Array Variable := #[]
  outlives : Array (Term × Term) := #[]
  deriving Repr, DecidableEq

abbrev M := StateT State (Except String)

private def lift (value : Except String α) : M α :=
  match value with | .ok value => pure value | .error error => throw error

def freshUniverse : M Universes.Scope := do
  let state ← get
  let scope := Universes.enter state.lastUniverse
  set {state with lastUniverse := scope.current}
  pure scope

def fresh (sort : ArgSort) (createdIn : Nat) : M Term := do
  unless sort != .aggregate do throw "aggregate cannot be an inference variable"
  let state ← get
  unless createdIn <= state.lastUniverse do throw "inference variable universe has not been allocated"
  let id := state.variables.size
  set {state with variables := state.variables.push ⟨sort,createdIn,none⟩}
  pure (.inference sort id)

def resolve (state : State) : Nat → Term → Except String Term
  | 0, _ => throw "inference assignment resolution exhausted"
  | fuel + 1, term => do
    match term with
    | .inference sort id =>
      let some entry := state.variables[id]? | throw "inference variable identity is absent"
      unless entry.sort == sort do throw "inference variable sort mismatch"
      if let some value := entry.assignment then resolve state fuel value else pure term
    | .node sort tag payload children =>
      return .node sort tag payload (← children.mapM (resolve state fuel))
    | .definition sort tag identity children =>
      return .definition sort tag identity (← children.mapM (resolve state fuel))
    | .binder variables body => return .binder variables (← resolve state fuel body)
    | _ => pure term

private def occurs (wanted : Nat) : Nat → Term → Except String Bool
  | 0, _ => throw "inference occurs traversal exhausted"
  | fuel + 1, term => do
    match term with
    | .inference _ id => pure (wanted == id)
    | .node _ _ _ children | .definition _ _ _ children => children.anyM (occurs wanted fuel)
    | .binder _ body => occurs wanted fuel body
    | _ => pure false

private def visible (createdIn : Nat) : Nat → Term → Except String Bool
  | 0, _ => throw "inference placeholder visibility traversal exhausted"
  | fuel + 1, term => do
    match term with
    | .placeholder _ universeIndex .. => pure (universeIndex <= createdIn)
    | .node _ _ _ children | .definition _ _ _ children =>
      return !(← children.anyM fun child => return !(← visible createdIn fuel child))
    | .binder _ body => visible createdIn fuel body
    | _ => pure true

/-- Revisit every assignment, since a later assignment can reveal a placeholder
inside a term assigned earlier. Checking only the newest variable is insufficient. -/
def assignmentsVisible (state : State) (fuel : Nat) : Except String Bool := do
  for entry in state.variables do
    if let some assignment := entry.assignment then
      let value ← resolve state fuel assignment
      unless ← visible entry.createdIn fuel value do return false
  pure true

/-- A failed equality assignment restores its input state. Resource exhaustion
and malformed variable references remain errors rather than negative answers. -/
def assign (fuel id : Nat) (value : Term) : M Bool := do
  let before ← get
  let some entry := before.variables[id]? | throw "assigned inference variable is absent"
  unless entry.assignment.isNone do throw "assigned inference variable is already resolved"
  let value ← lift (resolve before fuel value)
  unless value.sort == entry.sort do return false
  if value == .inference entry.sort id then return true
  if ← lift (occurs id fuel value) then return false
  if bounded : id < before.variables.size then
    let after := {before with variables := before.variables.set id {entry with assignment := some value} bounded}
    unless ← lift (assignmentsVisible after fuel) do return false
    set after
    pure true
  else throw "assigned inference variable index is absent"

private def openWith (variables : Array BoundVariable) (replacements : Array Term) :
    Nat → Nat → Term → Except String Term
  | 0, _, _ => throw "existential binder opening exhausted"
  | fuel + 1, depth, term => do
    match term with
    | .bound sort (.Bound index) position _ =>
      if index < depth then return term
      if index > depth then
        let .bound sort _ position identity := term | throw "bound variable shape disappeared"
        return .bound sort (.Bound (index - 1)) position identity
      let some entry := variables[position]? | throw "existential bound variable is absent"
      let expected := match entry with
        | .type _ => ArgSort.type | .region _ => .region | .constant => .constant
      let some replacement := replacements[position]? | throw "existential replacement is absent"
      unless expected == sort && replacement.sort == sort do throw "existential bound variable sort mismatch"
      pure replacement
    | .bound _ .Canonical .. => throw "canonical variable cannot open a source binder"
    | .binder inner body => return .binder inner (← openWith variables replacements fuel (depth + 1) body)
    | .node sort tag payload children =>
      return .node sort tag payload (← children.mapM (openWith variables replacements fuel depth))
    | .definition sort tag identity children =>
      return .definition sort tag identity (← children.mapM (openWith variables replacements fuel depth))
    | _ => pure term

/-- Infer the left side of a binder relation after the right side has entered
its forall universe. The fresh variables can name precisely that new universe. -/
def instantiateBinder (createdIn fuel : Nat) (variables : Array BoundVariable)
    (body : Term) : M Term := do
  let mut replacements := #[]
  for entry in variables do
    let sort := match entry with
      | .type _ => ArgSort.type | .region _ => .region | .constant => .constant
    replacements := replacements.push (← fresh sort createdIn)
  lift (openWith variables replacements fuel 0 body)

def constrainOutlives (longer shorter : Term) : M Unit := do
  unless longer.sort == .region && shorter.sort == .region do
    throw "outlives constraint contains a non-region"
  modify fun state => {state with outlives := state.outlives.push (longer,shorter)}

private def region (state : State) (fuel : Nat) (term : Term) : Except String RegionLeakCheck.Region := do
  match ← resolve state fuel term with
  | .placeholder .region universeIndex variableIndex _ => pure (.placeholder universeIndex variableIndex)
  | .inference .region id =>
    let some entry := state.variables[id]? | throw "region inference variable is absent"
    pure (.inference id entry.createdIn)
  | .atom .region "static" "" => pure (.root 0)
  | .atom .region "erased" "" => pure (.root 1)
  | _ => throw "region constraint requires resolved supported region syntax"

/-- Construct the actual post-resolution outlives graph. A successful result
discharges only the pinned early leak check; ordinary region solving is separate. -/
def checkLeaks (state : State) (outerUniverse fuel : Nat) : Except String Unit := do
  let mut nodes := #[]
  let mut edges := #[]
  for (longer,shorter) in state.outlives do
    let left ← region state fuel longer
    let right ← region state fuel shorter
    let leftId := match nodes.findIdx? (· == left) with
      | some id => id | none => nodes.size
    if leftId == nodes.size then nodes := nodes.push left
    let rightId := match nodes.findIdx? (· == right) with
      | some id => id | none => nodes.size
    if rightId == nodes.size then nodes := nodes.push right
    edges := edges.push ⟨leftId,rightId⟩
  RegionLeakCheck.check outerUniverse nodes edges

end Miri.Input.TraitSelection.Inference
