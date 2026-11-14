import Miri.ABI.ExternAbi

/-! Argument construction in pinned rustc_ty_utils/src/abi.rs:532–600,
`fn_abi_new_uncached`. Logical types only: virtual receiver thinning, layout
and target passing-mode classification remain separate required operations. -/
namespace Miri.ABI

structure SignatureSeed (Ty : Type) where
  inputs : Array Ty
  output : Ty
  abi : ExternAbi
  cVariadic : Bool
  deriving BEq, Repr, DecidableEq

structure PlannedSignature (Ty : Type) where
  inputs : Array Ty
  output : Ty
  fixedCount : Nat
  abi : ExternAbi
  cVariadic : Bool
  deriving BEq, Repr, DecidableEq

namespace SignatureSeed

/-- Source RustCall tuple splatting, variadic extras and injected caller
location. Tuple inspection uses the immutable source type arena. -/
def plan (signature : SignatureSeed Ty) (extra : Array Ty)
    (callerLocation : Option Ty) (tupleFields : Ty → Option (Array Ty)) :
    Except String (PlannedSignature Ty) := do
  let (fixed, extras) ← if signature.abi == .RustCall then do
      unless !signature.cVariadic && extra.isEmpty do
        throw "RustCall ABI requires nonvariadic signature and no extra arguments"
      let some last := signature.inputs.back?
        | throw "RustCall ABI requires a final tuple input"
      let some tuple := tupleFields last
        | throw "RustCall ABI final input is not a tuple"
      pure (signature.inputs.pop, tuple)
    else do
      unless signature.cVariadic || extra.isEmpty do
        throw "nonvariadic ABI received extra arguments"
      pure (signature.inputs, extra)
  let actual := fixed ++ extras
  let actual := match callerLocation with
    | none => actual
    | some ty => actual.push ty
  pure ⟨actual, signature.output, fixed.size, signature.abi, signature.cVariadic⟩

end SignatureSeed
end Miri.ABI
