import Miri.Input.SourceEnvironment.Material
import Miri.Input.TraitSelection.Codec
import Miri.Input.TraitSelection.Substitution

/-! Raw declaration predicate scopes. The parent relationship is source generic
metadata, not a solved ParamEnv result. Parent clauses retain their original
prefix parameter indices; only explicit instantiation applies actual arguments. -/
namespace Miri.Input.SourceEnvironment
open GenericSubstitution TraitSelection


private def assemble (lookup : Lookup) : Nat → Array DefinitionIdentity →
    DefinitionIdentity → Except String (Array Clause)
  | 0, _, _ => .error "source predicate parent traversal exhausted"
  | fuel + 1, active, definition => do
    if active.contains definition then throw "source predicate parent cycle"
    let material ← lookup definition
    Codec.validateClauses material.parameters material.ownPredicates
    unless material.parent == material.genericParent do
      throw "source predicate and generic parents require unsupported argument rebasing"
    let mut own := material.ownPredicates
    if material.isTrait then
      unless material.parameters[0]? == some .type do throw "source trait scope has no type Self parameter"
      let arguments := material.parameters.mapIdx fun index sort => Term.parameter sort index
      own := own.push ⟨#[],.trait ⟨.positive,⟨definition,arguments⟩⟩⟩
    let inherited ← match material.parent with
      | none => pure #[]
      | some parent => do
        let source ← lookup parent.definition
        unless parent.parameterCount == source.parameters.size do
          throw "source predicate parent parameter count mismatch"
        unless parent.parameterCount <= material.parameters.size do
          throw "source predicate parent exceeds child parameter scope"
        unless material.parameters.take parent.parameterCount == source.parameters do
          throw "source predicate parent parameter sorts are not a child prefix"
        assemble lookup fuel (active.push definition) parent.definition
    pure (inherited ++ own)

/-- Collect source-explicit inherited clauses and the pinned synthesized trait
self-clause. Inferred outlives are not reconstructed here; this is not a complete
non-erasing ParamEnv. No bound is normalized, selected or proved. -/
def predicates (lookup : Lookup) (fuel : Nat) (definition : DefinitionIdentity) :
    Except String (Array Clause) := assemble lookup fuel #[] definition

/-- Instantiate the complete source parent chain with explicitly supplied
arguments. This does not silently manufacture erased regions or defaults. -/
def instantiate (lookup : Lookup) (fuel : Nat) (definition : DefinitionIdentity)
    (arguments : Array Term) : Except String (Array Clause) := do
  let material ← lookup definition
  unless material.parameters.size == arguments.size do throw "source predicate argument count mismatch"
  for (parameter, argument) in material.parameters.zip arguments do
    unless parameter == argument.sort do throw "source predicate argument sort mismatch"
  let clauses ← predicates lookup fuel definition
  Substitution.clauses fuel arguments clauses
end Miri.Input.SourceEnvironment
