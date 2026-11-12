import Miri.ABI.StructLayout

/-! Pinned rustc_abi/src/layout.rs:343–400 selects the struct calculator for
an enum with at most one present variant and no C/integer representation.
The empty/absent case uses never_type, retaining its exact Empty variant shape.
This module does not classify tagged or niche-filled multi-variant enums. -/
namespace Miri.ABI.UnivariantEnumLayout

def compute (target : RuntimeTargetDataLayout) (variants : Array (Array LayoutData))
    (repr : UnivariantLayout.Representation)
    (niches : StructLayout.NicheOptimizations) : Except String LayoutData := do
  unless repr.flags &&& (1 + 2 + 64) == 0 && !repr.integerRepresentation do
    throw "univariant enum layout requires a non-C/non-integer/non-SIMD representation"
  unless repr.pack.isNone do throw "packed enum representation is invalid"
  unless variants.size ≤ 1 do throw "tagged or niche-filled enum layout requires its own calculator"
  let some fields := variants[0]? | return ← PrimitiveLayout.compute target "never"
  if fields.any (·.uninhabited) && fields.all (·.is1zst) then
    return ← PrimitiveLayout.compute target "never"
  StructLayout.compute target fields repr 0 true true niches

end Miri.ABI.UnivariantEnumLayout
