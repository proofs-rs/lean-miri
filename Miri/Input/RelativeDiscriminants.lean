import Miri.Input.AdtDeclaration
import Miri.Input.StructuralDiscriminantType

/-! Pinned rustc_middle/ty/adt.rs::discriminants starts at zero and
increments once for each non-explicit variant. Relative distances are raw
source consistency evidence, rather than independently evaluated answers.
Explicit expressions remain a CTFE obligation. -/
namespace Miri.Input.RelativeDiscriminants

def values (pointerBits : Nat) (declaration : AdtDeclaration.Material) : Except String (Option (Array (BitVec 128))) := do
  unless declaration.kind == .enumKind do throw "relative discriminants requested for non-enum"
  declaration.validateRaw
  if declaration.variants.any (fun variant => match variant.discriminant with
      | .explicit _ => true | _ => false) then return none
  unless [16,32,64].contains pointerBits do throw "relative discriminant target pointer width unsupported"
  let _ ← StructuralDiscriminantType.enumKey declaration.representation
  let (bits,signed) := match declaration.representation.integer with
    | none => (pointerBits,true)
    | some (.pointerSized signed) => (pointerBits,signed)
    | some (.fixed _ bits signed) => (bits,signed)
  unless declaration.variantCount ≤ 2^(bits - (if signed then 1 else 0)) do
    throw "default relative discriminants exceed declared integer representation"
  let result ← declaration.variants.zipIdx.mapM fun (variant,index) => do
    let .relative distance := variant.discriminant
      | throw "source discriminant constructor changed during traversal"
    unless distance == index do throw "raw default relative discriminant distance differs from physical index"
    pure (BitVec.ofNat 128 index)
  return some result
end Miri.Input.RelativeDiscriminants
