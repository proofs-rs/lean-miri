import Miri.Input.RuntimeArrayTypes

/-! Pinned rustc_ty_utils/src/abi.rs::arg_attrs_for_rust_scalar and
rustc_target/src/callconv/mod.rs::adjust_for_rust_abi, nonpointer ScalarPair
branch. Larger returns and pointer components require additional rules. -/
namespace Miri.Input.WorldAggregateAbi
open Miri.ABI

def nonPointerPair (layout : TyAndLayout TypeId) : Except String (ArgAbi TypeId) := do
  let .ScalarPair (a := a) (b := b) (bOffset := _) := layout.layout.backendRepr
    | throw "nonpointer pair ABI requires a scalar-pair layout"
  unless layout.layout.size.bytes <= 16 do
    throw "large scalar-pair ABI requires indirect-return and deduced-attribute rules"
  for scalar in #[a,b] do
    if let .Pointer _ := scalar.primitive then
      throw "scalar-pair pointer ABI requires aggregate pointee information"
  pure (ArgAbi.new layout fun scalar _ =>
    { ArgAttributes.new with
      regular := if scalar.isUninitValid then 0 else 128
      argExt := if scalar.isBool then .Zext else .None })

end Miri.Input.WorldAggregateAbi
