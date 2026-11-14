import Miri.Input.Model.Types
import Miri.ABI.Layout
import Miri.ABI.PatternLayout

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

/-- Material and appended pattern constructors share the pinned layout rule.
Endpoint identities and scalar widths are checked against the same World. -/
def compute (constant : TypeConstantId → Except String MIR.TypeConst)
    (target : Miri.ABI.RuntimeTargetDataLayout) (base : TypeId)
    (layout : Miri.ABI.LayoutData) (pattern : CompilerPattern) : Except String Miri.ABI.LayoutData := do
  match pattern with
  | .notNull => Miri.ABI.PatternLayout.notNull target layout
  | .range start finish =>
    let start ← endpoint constant base layout.size.bytes.toNat start
    let finish ← endpoint constant base layout.size.bytes.toNat finish
    Miri.ABI.PatternLayout.range target layout start finish
  | .or patterns =>
    let ranges ← patterns.mapM fun pattern => do
      let .range start finish := pattern | throw "Or pattern contains a non-range source pattern"
      let start ← endpoint constant base layout.size.bytes.toNat start
      let finish ← endpoint constant base layout.size.bytes.toNat finish
      pure (start,finish)
    Miri.ABI.PatternLayout.orRanges target layout ranges

end Miri.Input.PatternLayoutMaterial
