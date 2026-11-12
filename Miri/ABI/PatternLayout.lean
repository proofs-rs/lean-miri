import Miri.ABI.Layout

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd,
`rustc_ty_utils/src/layout.rs` PatternKind::NotNull and PatternKind::Range.
The caller supplies source-evaluated scalar endpoints; this module does not
interpret a normalized compiler answer as an endpoint expression. The source const evaluator is a separate operation. -/
namespace Miri.ABI.PatternLayout

private def withRange (target : RuntimeTargetDataLayout) (scalar : Scalar)
    (range : WrappingRange) : Except String (Scalar × Niche) := do
  let scalar ← scalar.setValidRange range |>.mapError reprStr
  let range ← scalar.validRange target |>.mapError reprStr
  pure (scalar, {offset := Size.ZERO, value := scalar.primitive, validRange := range})

def notNull (target : RuntimeTargetDataLayout) (base : LayoutData) : Except String LayoutData := do
  let (backend, niche) ← match base.backendRepr with
    | .Scalar scalar => do
      let range ← scalar.validRange target |>.mapError reprStr
      let (scalar, niche) ← withRange target scalar {range with start := 1}
      pure (.Scalar scalar, niche)
    | .ScalarPair (a := a) (b := b) (bOffset := offset) => do
      let range ← a.validRange target |>.mapError reprStr
      let (a, niche) ← withRange target a {range with start := 1}
      pure (.ScalarPair (a := a) (b := b) (bOffset := offset), niche)
    | _ => throw "NotNull pattern requires a scalar or scalar-pair base layout"
  pure {base with backendRepr := backend, largestNiche := some niche, fields := .Arbitrary #[Size.ZERO] #[0]}

def range (target : RuntimeTargetDataLayout) (base : LayoutData)
    (start finish : U128) : Except String LayoutData := do
  let .Scalar scalar := base.backendRepr
    | throw "range pattern requires a scalar base layout"
  let (scalar, niche) ← withRange target scalar ⟨start,finish⟩
  if scalar.isSigned then
    let start ← base.size.signExtend start |>.mapError reprStr
    let finish ← base.size.signExtend finish |>.mapError reprStr
    unless start <= finish do throw "signed pattern range cannot wrap"
  else unless start.toNat <= finish.toNat do throw "unsigned pattern range cannot wrap"
  pure {base with backendRepr := .Scalar scalar, largestNiche := some niche, fields := .Arbitrary #[Size.ZERO] #[0]}

/-- The pinned provider accepts exactly two signed ranges, orders their raw
unsigned endpoints, then forms one interval across the signed overflow site. -/
def orRanges (target : RuntimeTargetDataLayout) (base : LayoutData)
    (ranges : Array (U128 × U128)) : Except String LayoutData := do
  let .Scalar scalar := base.backendRepr
    | throw "Or pattern requires a scalar base layout"
  unless scalar.isSigned do throw "Or patterns require a signed integer base"
  let #[left,right] := ranges | throw "Or pattern requires exactly two ranges"
  let ordered := left.1.toNat < right.1.toNat ||
    (left.1 == right.1 && left.2.toNat <= right.2.toNat)
  let (first,second) := if ordered then (left,right) else (right,left)
  let minimum ← base.size.signedIntMin |>.mapError toString
  let minimum ← base.size.truncate (BitVec.ofInt 128 minimum) |>.mapError toString
  let (first,second) := if second.1 == minimum then (second,first) else (first,second)
  let firstEnd ← base.size.signExtend first.2 |>.mapError toString
  let secondStart ← base.size.signExtend second.1 |>.mapError toString
  unless firstEnd < secondStart do throw "Or pattern ranges overlap"
  let maximum ← base.size.signedIntMax |>.mapError toString
  unless second.2 == BitVec.ofInt 128 maximum do
    throw "Or pattern positive range does not end at signed maximum"
  let (scalar,niche) ← withRange target scalar ⟨second.1,first.2⟩
  pure {base with
    backendRepr := .Scalar scalar, largestNiche := some niche
    fields := .Arbitrary #[Size.ZERO] #[0]}

end Miri.ABI.PatternLayout
