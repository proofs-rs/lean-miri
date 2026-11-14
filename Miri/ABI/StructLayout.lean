import Miri.ABI.UnivariantLayout

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd,
`rustc_abi/src/layout.rs::layout_of_struct`. This is the calculator wrapper,
not the rustc_ty_utils declaration/environment query selecting alwaysSized or
niche optimizations. Callers must derive those from raw source material before
invoking this operation; absent declaration evidence cannot default to enabled
niches or a sized struct. -/
namespace Miri.ABI.StructLayout

inductive NicheOptimizations where
  | enabled | disabled
  deriving Repr, DecidableEq

private def hideScalar (target : RuntimeTargetDataLayout) (value : Scalar) :
    Except String Scalar := do
  match value with
  | .Union => pure value
  | .Initialized (value := primitive) =>
    let size ← primitive.size target |>.mapError toString
    let range ← WrappingRange.full size |>.mapError reprStr
    pure (.Initialized (value := primitive) (validRange := range))

private def hideBackend (target : RuntimeTargetDataLayout) (backend : BackendRepr) :
    Except String BackendRepr := do
  match backend with
  | .Scalar scalar => return .Scalar (← hideScalar target scalar)
  | .ScalarPair (a := a) (b := b) (bOffset := offset) =>
    return .ScalarPair (a := ← hideScalar target a) (b := ← hideScalar target b) (bOffset := offset)
  | .SimdVector (element := element) (count := count) =>
    return .SimdVector (element := ← hideScalar target element) (count := count)
  | .SimdScalableVector (element := element) (count := count) (numberOfVectors := vectors) =>
    return .SimdScalableVector (element := ← hideScalar target element) (count := count)
      (numberOfVectors := vectors)
  | .Memory => pure backend

def compute (target : RuntimeTargetDataLayout) (fields : Array LayoutData)
    (repr : UnivariantLayout.Representation) (variantIndex : Nat)
    (isEnum alwaysSized : Bool) (niches : NicheOptimizations) : Except String LayoutData := do
  let kind := if isEnum || fields.isEmpty || alwaysSized then
    UnivariantLayout.Kind.alwaysSized else .maybeUnsized
  let layout ← UnivariantLayout.compute target fields repr kind
  let layout := {layout with variants := .Single variantIndex}
  if niches == .enabled then return layout
  return {layout with backendRepr := ← hideBackend target layout.backendRepr, largestNiche := none}

end Miri.ABI.StructLayout
