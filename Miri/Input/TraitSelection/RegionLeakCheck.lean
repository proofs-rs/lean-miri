import Miri.Input.GenericSubstitution

/-! Placeholder leak rejection from the pinned region constraint collector
`rustc_infer/src/infer/region_constraints/leak_check.rs` (8144389c895d).
The compiler condenses the outlives graph into SCCs and propagates successor
universes/placeholders. This finite implementation instead visits the reachable
nodes from every new placeholder, checking the same two forbidden patterns:
`P1: P2` with distinct placeholders, and `P1: R` where R cannot name P1.
Edges have the actual outlives direction. `R: P1` alone is permitted, since R may
be `'static`. Graph construction, inference variable resolution and ordinary
region solving are separate requirements; this module implements only the
collector's early leak rejection on a supplied resolved constraint graph. -/
namespace Miri.Input.TraitSelection.RegionLeakCheck

inductive Region where
  | root (identity : Nat)
  | placeholder (universeIndex variableIndex : Nat)
  | inference (identity createdIn : Nat)
  deriving Repr, DecidableEq

private def Region.universeIndex : Region → Nat
  | .root _ => 0
  | .placeholder value _ | .inference _ value => value

structure Constraint where
  longer : Nat
  shorter : Nat
  deriving Repr, DecidableEq

private def reachable (nodes : Array Region) (edges : Array Constraint) (start : Nat) :
    Except String (Array Nat) := do
  unless start < nodes.size do throw "region leak graph start is absent"
  let mut reached := #[start]
  -- Every node enters the queue at most once. There can therefore be no more
  -- than nodes.size nonempty queue positions, including cycles and self-edges.
  for cursor in [:nodes.size] do
    let some current := reached[cursor]? | break
    for edge in edges do
      if edge.longer != current || reached.contains edge.shorter then continue
      reached := reached.push edge.shorter
  pure reached

/-- Empty success means only that the graph contains neither pinned leak
pattern. It does not discharge ordinary outlives or trait obligations. -/
def check (outerUniverse : Nat) (nodes : Array Region) (edges : Array Constraint) :
    Except String Unit := do
  for edge in edges do
    unless edge.longer < nodes.size && edge.shorter < nodes.size do
      throw "region leak constraint endpoint is absent"
  for (source,index) in nodes.zipIdx do
    let .placeholder sourceUniverse sourceVariable := source | continue
    if sourceUniverse <= outerUniverse then continue
    for target in ← reachable nodes edges index do
      let some region := nodes[target]? | throw "region leak reachable node is absent"
      unless sourceUniverse <= region.universeIndex do
        throw "placeholder outlives a region that cannot name its universe"
      if let .placeholder targetUniverse targetVariable := region then
        unless sourceUniverse == targetUniverse && sourceVariable == targetVariable do
          throw "distinct higher-ranked placeholders are constrained to outlive each other"

end Miri.Input.TraitSelection.RegionLeakCheck
