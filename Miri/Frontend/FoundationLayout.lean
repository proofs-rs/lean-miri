import Miri.Frontend.FoundationTarget
import Miri.Frontend.FoundationAggregateLayout
import Miri.Frontend.FoundationPointer
import Miri.Frontend.FoundationDynMetadata

/-! Pure size/ABI alignment queries over structural foundation material.
Target facts use the fixed interpreter runtime target bridge;
array sizing follows rustc_abi/src/layout.rs::layout_of_array_like.
This is deliberately not a Rust aggregate field-layout implementation. -/
namespace Miri.Frontend.Foundation

structure FoundationLayout where
  size : Nat
  align : Nat
  deriving Repr, DecidableEq

private def integerAlign (target : ABI.RuntimeTargetDataLayout) (width : Nat) : Except String Nat := do
  let align ← match width with
    | 8 => pure target.i8Align
    | 16 => pure target.i16Align
    | 32 => pure target.i32Align
    | 64 => pure target.i64Align
    | 128 => pure target.i128Align
    | _ => throw "unsupported integer alignment width"
  return (← align.bytes.mapError toString).toNat

private def integerWidth (target : ABI.RuntimeTargetDataLayout) (kind name : String) : Except String Nat := do
  if (kind == "int" && name == "isize") || (kind == "uint" && name == "usize") then
    return target.base.pointerWidth.bits.toNat
  let names := if kind == "int" then #["i8", "i16", "i32", "i64", "i128"]
    else if kind == "uint" then #["u8", "u16", "u32", "u64", "u128"] else #[]
  let widths := #[8, 16, 32, 64, 128]
  for (candidate, width) in names.toList.zip widths.toList do
    if candidate == name then return width
  throw s!"unsupported foundation integer {kind} {name}"

/-- Compute only requested layouts. Nonempty Rust tuples can reorder fields;
without the complete pinned aggregate algorithm they remain explicit errors.
Pointers to supported Sized types and str are supported. str has its unsized
zero-size layout lower bound; floats, other unsized types and nominal types
remain unsupported. Arrays require a supported Sized element. -/
private def layoutCore (target : ABI.RuntimeTargetDataLayout) (allowDyn : Bool) (ty : ConcreteType) : Except String FoundationLayout := do
  target.validate.mapError toString
  let bound := target.base.objSizeBound.toNat
  go bound 1024 ty
where
  go (bound fuel : Nat) (ty : ConcreteType) : Except String FoundationLayout := do
    let .succ remaining := fuel | throw "foundation layout recursion exhausted"
    match ty with
    | .closure _ arguments =>
      let some (.tuple upvars) := arguments.back? | throw "closure upvars argument absent"
      unless arguments.size ≥ 3 do throw "closure synthetic arguments absent"
      let some (.primitive "int" kind) := arguments[arguments.size - 3]?
        | throw "closure kind type absent"
      unless #["i8", "i16", "i32"].contains kind do throw "closure kind encoding invalid"
      let some (.functionPointer _ _ safety "rust_call" false) := arguments[arguments.size - 2]?
        | throw "closure RustCall signature absent"
      unless safety == "safe" || safety == "unsafe" do throw "closure signature safety invalid"
      go bound remaining (.tuple upvars)
    | .nominal _ _ => throw "nominal component requires document physical query"
    | .patternNotNull _ => throw "general constrained-pattern layout unsupported"
    | .primitive "str" "" =>
      return ⟨0, ← integerAlign target 8⟩
    | .primitive kind name =>
      let width ← if kind == "bool" && name == "" then pure 8
        else if kind == "char" && name == "" then pure 32
        else integerWidth target kind name
      let align ← integerAlign target width
      return ⟨width / 8, align⟩
    | .array element length =>
      unless length < 2 ^ target.base.pointerWidth.bits.toNat do throw "array length exceeds target usize"
      match element with
      | .primitive "str" "" | .dynamicObject _ => throw "array element is unsized"
      | _ => pure ()
      let elem ← go bound remaining element
      let size := elem.size * length
      unless size < bound do throw "foundation array layout size overflow"
      return ⟨size, elem.align⟩
    | .tuple elements =>
      if elements.isEmpty then
        let align ← target.aggregateAlign.bytes.mapError toString
        return ⟨0, align.toNat⟩
      if elements.size > 1 then
        let mut fields := #[]
        for element in elements do
          match element with
          | .primitive .. | .pointer .. | .functionPointer .. => pure ()
          | _ => throw "aggregate sizing supports only scalar/pair fields"
          let f ← go bound remaining element
          fields := fields.push (f.size,f.align)
        let aggregate ← target.aggregateAlign.bytes.mapError toString
        let (size,align) ← scalarAggregateSize aggregate.toNat bound fields true
        return ⟨size,align⟩
      let some element := elements[0]? | throw "tuple element absent"
      let layout ← go bound remaining element
      let aggregate ← target.aggregateAlign.bytes.mapError toString
      unless aggregate.toNat ≤ layout.align do throw "singleton tuple aggregate alignment unsupported"
      return layout
    | .dynamicObject _ => return ⟨0, ← integerAlign target 8⟩
    | .functionPointer _ _ safety abi variadic =>
      unless (safety == "safe" || safety == "unsafe") && (abi == "rust" || abi == "rust_call") && !variadic do
        throw "unsupported physical function-pointer signature"
      let spec ← (target.pointerSpecIn target.instructionAddressSpace).mapError toString
      return ⟨spec.pointerSize.bytes.toNat, (← spec.pointerAlign.bytes.mapError toString).toNat⟩
    | .pointer kind pointee =>
      let _ ← pointerKindInfo kind
      -- Every supported pointee is Sized; unknown/unsized cases fail recursively.
      let _ ← go bound remaining pointee
      let spec ← (target.pointerSpecIn ABI.AddressSpace.ZERO).mapError toString
      let align ← spec.pointerAlign.bytes.mapError toString
      if let .dynamicObject _ := pointee then
        unless allowDyn do throw "dyn pointer requires source metadata declaration evidence"
        let aggregate ← target.aggregateAlign.bytes.mapError toString
        unless spec.pointerSize.bytes.toNat == align.toNat && aggregate.toNat == 1 do
          throw "dyn metadata wrapper layout requires supported pointer/aggregate alignments"
        return ⟨2 * spec.pointerSize.bytes.toNat, align.toNat⟩
      if let .primitive "str" "" := pointee then
        let bits := target.pointerOffset.bytes.toNat * 8
        let metadataAlign ← integerAlign target bits
        let metadataSize := bits / 8
        let offset := (spec.pointerSize.bytes.toNat + metadataAlign - 1) / metadataAlign * metadataAlign
        let aggregate ← target.aggregateAlign.bytes.mapError toString
        let pairAlign := max align.toNat (max metadataAlign aggregate.toNat)
        return ⟨(offset + metadataSize + pairAlign - 1) / pairAlign * pairAlign, pairAlign⟩
      return ⟨spec.pointerSize.bytes.toNat, align.toNat⟩

/-- Target-only queries cannot supply a dyn metadata declaration contract. -/
def layoutOfRuntime (target : ABI.RuntimeTargetDataLayout) (ty : ConcreteType) : Except String FoundationLayout :=
  layoutCore target false ty

/-- Dyn-pointer queries additionally validate finite source declarations. -/
def layoutOfDocument (d : Document) (ty : ConcreteType) : Except String FoundationLayout := do
  let needed ← requiresDynMetadata ty
  if needed then validateDynMetadataSource d
  layoutCore (← runtimeTargetOfTarget d.target) needed ty

/-- Foundation queries require complete finite target evidence; missing or
inconsistent evidence cannot recover LLVM parser defaults. -/
def layoutOf (target : Target) (ty : ConcreteType) : Except String FoundationLayout := do
  layoutOfRuntime (← runtimeTargetOfTarget target) ty

/-- Resolve and instantiate a finite source type before its demand-time query. -/
def layoutOfType (d : Document) (id : Nat) (types : Array (Option ConcreteType))
    (constants : Array (Option Nat)) : Except String FoundationLayout := do
  layoutOfDocument d (← instantiate types constants (← typeExpr d id))

end Miri.Frontend.Foundation
