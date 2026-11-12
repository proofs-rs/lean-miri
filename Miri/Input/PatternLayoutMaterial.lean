import Miri.Input.Model.Types
import Miri.ABI.Layout

/-! Raw `ConstKind::Value` scalar endpoints for pinned rustc
8144389c895da997dbdecaa635e41d6a50be6ffd `layout_of` pattern ranges.
This accepts no evaluated aliases, expression constants or summary values. -/
namespace Miri.Input.PatternLayoutMaterial

def endpoint (constant : TypeConstantId → Except String MIR.TypeConst)
    (base : TypeId) (byteWidth : Nat) (id : TypeConstantId) : Except String ABI.U128 := do
  unless byteWidth > 0 && byteWidth <= 16 do
    throw "pattern endpoint scalar width unsupported"
  let .Value ty tree ← constant id
    | throw "pattern endpoint requires source constant evaluation"
  unless ty == base do throw "pattern endpoint value type differs from base type"
  unless tree.root == 0 && tree.nodes.size == 1 do
    throw "pattern endpoint value is not a canonical scalar valtree"
  let some (Miri.MIR.ValTreeNode.Leaf bits bytes) := tree.nodes[0]?
    | throw "pattern endpoint value is not a scalar leaf"
  unless bytes == byteWidth && bits < 2^(8 * byteWidth) do
    throw "pattern endpoint scalar value exceeds base width"
  pure (BitVec.ofNat 128 bits)

end Miri.Input.PatternLayoutMaterial
