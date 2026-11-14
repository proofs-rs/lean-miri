import Miri.ABI.RuntimeLayout

/-! Pinned rustc_middle::ty::layout.rs IntegerExt::discr_range_of_repr.
This computes the physical tag width from the raw repr and evaluated source
integer range. It does not evaluate explicit discriminant expressions. -/
namespace Miri.ABI.EnumDiscriminantLayout

private def larger (a b : Integer) : Integer :=
  if a.size.bytes.toNat < b.size.bytes.toNat then b else a

/-- `minNegative` is the signed i128 interpretation; `maxPositive` preserves
unsigned u128 syntax. Their distinction controls unsigned/signed tag selection. -/
def select (target : RuntimeTargetDataLayout) (repr : Option IntegerType)
    (reprC : Bool) (minNegative : Int) (maxPositive : U128) :
    Except String (Integer × Bool) := do
  unless Integer.signedMin .I128 ≤ minNegative && minNegative ≤ Integer.signedMax .I128 do
    throw "enum discriminant minimum does not fit i128"
  unless minNegative ≥ 0 || maxPositive.toNat ≤ (Integer.signedMax .I128).toNat do
    throw "no integer can represent the full enum discriminant range"
  let minimumBits : U128 := BitVec.ofInt 128 minNegative
  let unsignedFit := Integer.fitUnsigned (if minimumBits.toNat > maxPositive.toNat then minimumBits else maxPositive)
  let signedFit := larger (Integer.fitSigned minNegative) (Integer.fitSigned maxPositive.toInt)
  if let some attr := repr then
    let chosen ← (Integer.fromAttr target attr).mapError reprStr
    let fit := if attr.isSigned then signedFit else unsignedFit
    unless chosen.size.bytes.toNat ≥ fit.size.bytes.toNat do
      throw "integer repr is too small for the enum discriminant range"
    return (chosen,attr.isSigned)
  let atLeast := if reprC then target.cEnumMinSize else .I8
  if unsignedFit.size.bytes.toNat ≤ signedFit.size.bytes.toNat then
    return (larger unsignedFit atLeast,false)
  return (larger signedFit atLeast,true)

end Miri.ABI.EnumDiscriminantLayout
