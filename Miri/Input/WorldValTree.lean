import Miri.Input.WorldMirConstant
import Miri.Input.RuntimeMetadata

/-! Stateful ValTree conversion. Pinned valtrees.rs::valtree_to_const_value
returns ZST aggregates directly and peels the unique non-ZST field of scalar
tuples/structs. Field substitution may append syntax to this execution's World;
no allocation, layout answer or converted-value cache is retained here. -/
namespace Miri.Input.WorldValTree
open Miri.MIR Miri.ABI TypeArena

private def lift (value : Except String α) : WorldM α :=
  match value with | .ok value => pure value | .error error => throw error

private def canonicalRoot (tree : ValTree) : Except String ValTreeNode := do
  unless tree.root == 0 && tree.nodes.size == 1 do
    throw "ValTree conversion requires the canonical source node domain"
  let some root := tree.nodes[tree.root]? | throw "ValTree conversion source root is absent"
  pure root

def fromValue (runtime : RuntimeMetadata) : Nat → TyId → ValTree → WorldM ConstValue
  | 0, _, _ => throw "ValTree conversion traversal exhausted"
  | fuel + 1, ty, tree => do
    let world ← get
    let view ← lift (world.lookupType ty)
    if let .material source := view then
      if let .patternType base _ := source.shape then
        return ← fromValue runtime fuel base tree
    let kind ← lift (world.shapeKind ty)
    unless kind == .tuple || kind == .array || kind == .adt do
      return ← lift ((WorldMirConstant.fromValue world ty tree).mapError reprStr)
    let root ← lift (canonicalRoot tree)
    let .Branch branches := root | throw "aggregate ValTree source is not a branch"
    let parent ← runtime.layoutInWorld ty
    if parent.layout.isZst then return .ZeroSized
    let scalar := match parent.layout.backendRepr with | .Scalar _ => true | _ => false
    let isStructure ← if kind == .adt then do
      let source ← runtime.adtDeclarationInWorld ty
      pure (source.kind == .structKind)
      else pure (kind == .tuple)
    unless scalar && isStructure do
      throw "non-scalar ValTree conversion requires the CTFE allocation/interning machine"
    unless branches.size == parent.layout.fields.count do
      throw "scalar aggregate ValTree branch count differs from its source field domain"
    for (constantId,index) in branches.zipIdx do
      let field ← runtime.fieldLayoutForInWorld parent index
      unless field.layout.isZst do
        let constant ← lift ((← get).lookupConstant constantId)
        let .Value _ inner := constant | throw "scalar aggregate ValTree field is not a source Value"
        -- The compiler uses field.layout.ty, not the child Value's annotation.
        return ← fromValue runtime fuel field.ty inner
    throw "scalar aggregate ValTree has no non-ZST source field"

def evaluate (runtime : RuntimeMetadata) (span : SpanRef) (constant : MirConst) :
    WorldM (TyId × ConstValue) := do
  match constant with
  | .Ty _ id =>
    let source ← lift ((← get).lookupConstant id)
    match source with
    | .Value ty tree => return (ty, ← fromValue runtime 16384 ty tree)
    | _ => lift ((WorldMirConstant.evaluate (← get) span constant).mapError reprStr)
  | _ => lift ((WorldMirConstant.evaluate (← get) span constant).mapError reprStr)

end Miri.Input.WorldValTree
