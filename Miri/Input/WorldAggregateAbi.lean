import Miri.Input.RuntimeArrayTypes

/-! Pinned rustc_ty_utils/src/abi.rs::arg_attrs_for_rust_scalar and
rustc_target/src/callconv/mod.rs::adjust_for_rust_abi, primitive and bounded
raw-pointer ScalarPairs plus sized aggregate adjustment. -/
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

private def liftPure (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

private def sourceConstructor (id : TypeId) : RuntimeArrayTypes.CompilerM TypeArena.Constructor := do
  let arena := (← get).arena
  match ← liftPure (arena.lookupType id) with
  | .constructed constructor => pure constructor
  | .material source =>
    let some constructor ← liftPure (arena.materialKey source)
      | throw "raw pair field source constructor is unavailable"
    pure constructor

/-- Source raw pointer to slice/str: data component uses the raw-pointer
pointee rule at offset zero; usize metadata is a nonpointer scalar. No pointee,
Freeze, Unpin or projection answers enter this construction. -/
def rawSlicePointer (runtime : RuntimeMetadata) (layout : TyAndLayout TypeId) :
    RuntimeArrayTypes.CompilerM (ArgAbi TypeId) := do
  unless runtime.target.defaultAddressSpace == .ZERO && runtime.target.pointerSize.bytes == 8 do
    throw "wide raw pointer ABI requires the 64-bit data address space"
  for align in #[runtime.target.defaultAddressSpacePointerSpec.pointerAlign,
      runtime.target.i64Align,runtime.target.aggregateAlign,layout.layout.align.abi] do
    unless (← liftPure (align.bytes.mapError reprStr)) <= 8 do
      throw "wide raw pointer ABI alignment exceeds one register"
  let .rawPointer pointee _ ← sourceConstructor layout.ty
    | throw "wide raw pointer ABI requires a raw-pointer source constructor"
  let constructor ← sourceConstructor pointee
  unless (match constructor with | .slice _ | .str => true | _ => false) do
    throw "wide raw pointer ABI requires slice or str metadata"
  let usize ← liftPure (PrimitiveLayout.compute runtime.target "usize")
  let expected ← liftPure (PrimitiveLayout.pointer runtime.target false (some usize))
  unless layout.layout == expected do
    throw "wide raw pointer layout differs from its source-derived pointer/usize layout"
  let .ScalarPair (a := data) (b := metadata) (bOffset := offset) := layout.layout.backendRepr
    | throw "wide raw pointer requires scalar-pair storage"
  unless layout.layout.isSized && layout.layout.size.bytes == 16 && offset.bytes == 8 do
    throw "wide raw pointer storage differs from pointer-plus-usize"
  let .Initialized (value := .Pointer space) (validRange := range) := data
    | throw "wide raw pointer data component is not an initialized pointer"
  unless space == .ZERO do throw "wide raw pointer requires data address space zero"
  let .Initialized (value := .Int .I64 false) (validRange := _) := metadata
    | throw "wide raw pointer metadata component is not initialized usize"
  let attrs : ArgAttributes := {ArgAttributes.new with
    regular := 128 ||| (if range.contains 0 then 0 else 16)}
  pure ⟨layout,.Pair attrs {ArgAttributes.new with regular := 128}⟩

/-- Pinned pointee_info_at walks tuple fields by physical offsets. In this
bounded grammar every pointer-bearing field is a thin RawPtr: its recursive
answer is safe=None, size=0, align=1. References, wrappers and FnPtr value fields
remain unsupported. No material projection/pointee/trait answers are read. -/
def rawPointerPair (runtime : RuntimeMetadata) (layout : TyAndLayout TypeId) :
    RuntimeArrayTypes.CompilerM (ArgAbi TypeId) := do
  let .ScalarPair (a := a) (b := b) (bOffset := bOffset) := layout.layout.backendRepr
    | throw "raw pointer pair requires ScalarPair representation"
  unless layout.layout.isSized && layout.layout.size.bytes <= 16 do
    throw "raw pointer pair exceeds the direct aggregate bound"
  unless (match layout.layout.variants with | .Single _ => true | _ => false) do
    throw "raw pointer pair requires a single tuple variant"
  let .tuple children ← sourceConstructor layout.ty
    | throw "raw pointer pair requires a source tuple"
  unless children.size == 2 do throw "raw pointer pair requires exactly two fields"
  let .Arbitrary offsets _ := layout.layout.fields
    | throw "raw pointer pair requires explicit tuple field offsets"
  unless offsets.size == 2 do throw "raw pointer pair field offsets are malformed"
  let mut attrsA := none
  let mut attrsB := none
  let mut rawCount := 0
  for index in [:2] do
    let some child := children[index]? | throw "raw pointer pair source field is absent"
    let some offset := offsets[index]? | throw "raw pointer pair source offset is absent"
    let constructor ← sourceConstructor child
    let field ← RuntimeArrayTypes.liftType (RuntimeMetadata.layoutInWorld runtime child)
    let .Scalar scalar := field.layout.backendRepr
      | throw "raw pointer pair field is not a thin scalar"
    unless field.layout.size.bytes <= 8 do throw "raw pointer pair field exceeds one register"
    unless offset.bytes <= layout.layout.size.bytes do throw "raw pointer pair field offset exceeds its parent"
    unless field.layout.size.bytes <= layout.layout.size.bytes - offset.bytes do
      throw "raw pointer pair field storage exceeds its parent"
    if (match constructor with | .rawPointer .. => true | _ => false) then rawCount := rawCount + 1
    let arg ← match constructor with
      | .rawPointer .. => do
        let .Initialized (value := .Pointer space) (validRange := _) := scalar
          | throw "raw pointer pair field has no initialized pointer scalar"
        unless space == .ZERO do throw "raw pointer pair requires data address space zero"
        liftPure (ArgAbi.conservativePointerScalar field)
      | .bool | .char | .integer .. | .float .. => liftPure (ArgAbi.nonPointerScalar field 0)
      | _ => throw "raw pointer pair field is outside the source grammar"
    let .Direct attrs := arg.mode | throw "raw pointer pair field is not passed directly"
    if offset == Size.ZERO && scalar == a then
      unless attrsA.isNone do throw "raw pointer pair has duplicate first component"
      attrsA := some attrs
    else if offset == bOffset && scalar == b then
      unless attrsB.isNone do throw "raw pointer pair has duplicate second component"
      attrsB := some attrs
    else throw "raw pointer pair field does not match its physical scalar component"
  unless rawCount > 0 do throw "raw pointer pair has no raw-pointer field"
  let some first := attrsA | throw "raw pointer pair first component is absent"
  let some second := attrsB | throw "raw pointer pair second component is absent"
  pure ⟨layout,.Pair first second⟩

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
