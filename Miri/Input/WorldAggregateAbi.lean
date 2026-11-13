import Miri.Input.RuntimeArrayTypes

/-! Pinned rustc_ty_utils/src/abi.rs::arg_attrs_for_rust_scalar and
rustc_target/src/callconv/mod.rs::adjust_for_rust_abi, nonpointer ScalarPair
branch and sized aggregate adjustment. Pointer components require additional rules. -/
namespace Miri.Input.WorldAggregateAbi
open Miri.ABI

def nonPointerPair (layout : TyAndLayout TypeId) (isReturn : Bool := false) : Except String (ArgAbi TypeId) := do
  let .ScalarPair (a := a) (b := b) (bOffset := _) := layout.layout.backendRepr
    | throw "nonpointer pair ABI requires a scalar-pair layout"
  for scalar in #[a,b] do
    if let .Pointer _ := scalar.primitive then
      throw "scalar-pair pointer ABI requires aggregate pointee information"
  let arg := ArgAbi.new layout fun scalar _ =>
    { ArgAttributes.new with
      regular := if scalar.isUninitValid then 0 else 128
      argExt := if scalar.isBool then .Zext else .None }
  if isReturn && layout.layout.size.bytes > 16 then arg.makeIndirect else pure arg

/-- Pinned layout_is_noundef/fields_are_noundef, including padding and union
rejection. Field construction extends the execution World. -/
def layoutIsNoUndef : Nat → RuntimeMetadata → TyAndLayout TypeId →
    RuntimeArrayTypes.CompilerM Bool
  | 0,_,_ => throw "aggregate ABI initialization analysis exhausted"
  | fuel+1,runtime,layout => do
    match layout.layout.backendRepr with
    | .Scalar scalar => pure (!scalar.isUninitValid)
    | .ScalarPair (a := a) (b := b) (bOffset := _) =>
      let sizeA ← match a.primitive.size runtime.target with
        | .ok size => pure size | .error error => throw (reprStr error)
      let sizeB ← match b.primitive.size runtime.target with
        | .ok size => pure size | .error error => throw (reprStr error)
      pure (!a.isUninitValid && !b.isUninitValid &&
        sizeA.bytes + sizeB.bytes == layout.layout.size.bytes)
    | .Memory =>
      match layout.layout.fields with
      | .Primitive | .Union _ => pure false
      | .Array _ count =>
        if count == 0 then return true
        let child ← RuntimeArrayTypes.liftType (RuntimeMetadata.fieldLayoutForInWorld runtime layout 0)
        layoutIsNoUndef fuel runtime child
      | .Arbitrary offsets order =>
        unless (match layout.layout.variants with | .Single _ => true | _ => false) do return false
        let mut cursor : UInt64 := 0
        for index in order do
          let child ← RuntimeArrayTypes.liftType (RuntimeMetadata.fieldLayoutForInWorld runtime layout index)
          if child.layout.size.bytes == 0 then continue
          let some offset := offsets[index]? | throw "aggregate ABI field offset absent"
          unless offset.bytes == cursor do return false
          unless ← layoutIsNoUndef fuel runtime child do return false
          cursor := cursor + child.layout.size.bytes
        pure (cursor == layout.layout.size.bytes)
    | _ => pure false

/-- Pinned sized Memory adjustment on x86_64. The target's integer register
alignment can round the cast storage above the source size: i24 occupies four
bytes, so a fully initialized three-byte aggregate still lacks NoUndef. -/
def smallMemory (runtime : RuntimeMetadata) (layout : TyAndLayout TypeId) :
    RuntimeArrayTypes.CompilerM (ArgAbi TypeId) := do
  if layout.layout.isZst then return ArgAbi.initial layout
  unless layout.layout.isSized && layout.layout.size.bytes <= 8 do
    throw "small aggregate ABI requires a sized layout no larger than one register"
  let .Memory := layout.layout.backendRepr
    | throw "small aggregate ABI requires Memory representation"
  let unit : Reg := {kind := .Integer, size := layout.layout.size}
  let registerAlign ← match unit.align runtime.target with
    | .ok align => pure align | .error error => throw (reprStr error)
  let alignment := registerAlign.max runtime.target.aggregateAlign
  let castSize ← match layout.layout.size.alignTo alignment with
    | .ok size => pure size | .error error => throw (reprStr error)
  let initialized ← layoutIsNoUndef 16384 runtime layout
  let attrs : ArgAttributes := {ArgAttributes.new with
    regular := if initialized && castSize == layout.layout.size then 128 else 0}
  let rest : Uniform := {unit, total := layout.layout.size, isConsecutive := false}
  pure ⟨layout,.Cast 0 ⟨#[],none,rest,attrs⟩⟩

end Miri.Input.WorldAggregateAbi
