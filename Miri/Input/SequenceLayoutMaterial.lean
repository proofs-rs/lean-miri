import Miri.Input.Model.Types

/-! Canonical target-usize value material for array layout. Complex constant
expressions require the source const evaluator; their normalized count summary
cannot stand in for a raw value constructor. -/
namespace Miri.Input.SequenceLayoutMaterial

def arrayCount (isUsize : TypeId → Except String Bool)
    (constant : TypeConstantId → Except String MIR.TypeConst)
    (pointerBytes : Nat) (length : TypeConstantId) (identity : ArrayConstructor) :
    Except String UInt64 := do
  unless identity.canonicalValueConstructor do
    throw "array length requires source constant evaluation"
  unless pointerBytes > 0 && pointerBytes <= 8 do
    throw "array target usize width unsupported"
  let value ← constant length
  let .Value ty tree := value
    | throw "array canonical length is not a source value constant"
  unless ← isUsize ty do
    throw "array length source value type is not usize"
  unless tree.root == 0 && tree.nodes.size == 1 do
    throw "array length source value is not a canonical scalar valtree"
  let some (Miri.MIR.ValTreeNode.Leaf bits bytes) := tree.nodes[0]?
    | throw "array length source value is not a scalar leaf"
  unless bytes == pointerBytes && bits < 2^(8 * pointerBytes) && bits < 2^64 do
    throw "array length source value exceeds target usize"
  unless bits == identity.count do throw "array source constructor count disagrees with raw value"
  pure (UInt64.ofNat bits)

end Miri.Input.SequenceLayoutMaterial
