import Miri.Frontend.FoundationAbi

/-! Exact pass-mode material for the supported scalar/array subset of ordinary
Rust ABI on explicit x86_64 targets. Source: pinned rustc_ty_utils/src/abi.rs
`arg_attrs_for_rust_scalar` and rustc_target/src/callconv/mod.rs `ArgAbi::new`,
`adjust_for_rust_abi`, `cast_to_maybe_noundef`, revision
8144389c895da997dbdecaa635e41d6a50be6ffd.

This is a parametric component, not a document-to-interpreter FnAbi bridge:
physical identities still require a validated document-local type/layout registry.
It never allocates identities or copies precomputed compiler ABI answers. -/
namespace Miri.Frontend.Foundation

private def attributes (bits : Nat) (extension : Input.ArgumentExtensionKind := .none)
    (size : Nat := 0) (align : Option Nat := none) : Input.AbiAttributes :=
  ⟨bits, size, align, extension⟩

/-- Every accepted scalar is initialized; accepted arrays have neither padding
nor unions. Thus the exact-sized integer aggregate cast preserves NoUndef. -/
private def rustPassCore (target : Target)
    (ty : ConcreteType) (referenceOptLevel : Option String)
    (mode : Except String RustModeShape) : Except String Input.AbiPassMode := do
  let shape ← mode
  let empty : Input.AbiPassMode := ⟨.ignore, #[], none, none, none, none⟩
  match shape with
  | .ignore => return empty
  | .direct extendBool =>
    -- Raw pointers have no dereferenceable pointee and retain the full valid
    -- range. FnPtr excludes null in its scalar layout: NoUndef | NonNull.
    if let .pointer kind pointee := ty then
      let info ← pointerKindInfo kind
      if info.region.isSome then
        unless info.mutability == .Not && referenceOptLevel == some "No" do
          throw "shared thin reference ABI requires explicit OptLevel::No"
        let pointeeLayout ← layoutOf target pointee
        -- pointee_info_at skips Freeze at optNo, yielding size0. In both
        -- argument/return position the frozen=false branch adds no alias,
        -- NoFree, ReadOnly or capture flags. Deduced attributes affect only
        -- Indirect modes, never this Direct mode.
        return {empty with kind := .direct, attributes := #[attributes 144 .none 0
          (if pointeeLayout.align > 1 then some pointeeLayout.align else none)]}
    let bits := match ty with | .functionPointer .. => 144 | _ => 128
    return { empty with kind := .direct, attributes := #[attributes bits
      (if extendBool then .zeroExtend else .none)] }
  | .pair =>
    let .pointer kind pointeeTy := ty | throw "unsupported Rust ABI scalar-pair type"
    let info ← pointerKindInfo kind
    unless info.region.isSome && info.mutability == .Not && referenceOptLevel == some "No" do
      throw "shared pair ABI requires explicit OptLevel::No"
    let pointee ← layoutOf target pointeeTy
    let data := attributes 144 .none 0 (if pointee.align > 1 then some pointee.align else none)
    let metadata ← match pointeeTy with
      | .primitive "str" "" => pure (attributes 128)
      | .dynamicObject _ => do
        -- ty_and_layout_field gives the vtable scalar the type &'static
        -- [usize; vtable_min_entries]. At optNo its pointee size is zero;
        -- array alignment is usize alignment for every possible entry count.
        -- Thus no method count, allocation or method identity is invented.
        let runtime ← runtimeTargetOfTarget target
        let width := runtime.pointerOffset.bytes.toNat * 8
        let integer ← layoutOf target (.primitive "uint" s!"u{width}")
        pure (attributes 144 .none 0 (if integer.align > 1 then some integer.align else none))
      | _ => throw "unsupported Rust ABI pair metadata"
    return {empty with kind := .pair, attributes := #[data, metadata]}
  | .integerCast size =>
    let register : Input.AbiRegister := ⟨.integer, size * 8, none⟩
    let cast : Input.AbiCastTarget := ⟨#[], none, register, size, false, attributes 128⟩
    return { empty with kind := .cast, castTarget := some cast, padI32Count := some 0 }
  | .indirect =>
    let layout ← layoutOf target ty
    -- NoAlias | CapturesAddress | NonNull | NoUndef | NoFree.
    return { empty with
      kind := .indirect
      attributes := #[attributes 670 Input.ArgumentExtensionKind.none layout.size (some layout.align)]
      indirectMode := some .pointer }

/-- Explicit-target component; source metadata-dependent types fail closed. -/
def rustPassMode (target : Target) (architecture : String) (isReturn : Bool)
    (ty : ConcreteType) (referenceOptLevel : Option String := none) : Except String Input.AbiPassMode :=
  rustPassCore target ty referenceOptLevel (rustModeShape target architecture isReturn ty)

/-- Derive both the layout context and reference optimization input from the
same finite source document. Unknown/optimized reference modes remain errors. -/
def rustPassModeOfDocument (d : Document) (isReturn : Bool) (ty : ConcreteType) : Except String Input.AbiPassMode := do
  let needsReference := match ty with
    | .pointer kind _ => match pointerKindInfo kind with
      | .ok info => info.region.isSome
      | .error _ => false
    | _ => false
  let opt ← if needsReference then do
      let source ← d.source.getObjVal? "compilation"
      pure (some (← source.getObjValAs? String "opt_level"))
    else pure none
  rustPassCore d.target ty opt (rustModeShapeOfDocument d isReturn ty)

/-- IDs supplied here must already name this concrete type and its *physical*
layout in the same executable registry. Size/alignment checks alone cannot
establish this association. No registry validation or provenance claim is made
by this data structure or by `rustFunctionAbiComponent`. -/
structure AbiTypeBinding where
  type : ConcreteType
  typeId : Input.TypeId
  layoutId : Input.LayoutId

private def rustArgument (target : Target) (architecture : String) (isReturn : Bool)
    (binding : AbiTypeBinding) (referenceOptLevel : Option String) : Except String Input.AbiArgument := do
  return ⟨binding.typeId, binding.layoutId,
    ← rustPassMode target architecture isReturn binding.type referenceOptLevel⟩

/-- Parametric construction for a nonvariadic ordinary Rust item, without
track_caller, virtual receiver adjustment, extra arguments or deduced pointer
attributes. The caller must establish those signature facts and the binding
associations above; this API is not sufficient evidence for interpreter import. -/
def rustFunctionAbiComponent (target : Target) (architecture : String)
    (unwind : RustUnwindFacts) (arguments : Array AbiTypeBinding)
    (result : AbiTypeBinding) (referenceOptLevel : Option String := none) : Except String Input.FunctionAbi := do
  let ret ← rustArgument target architecture true result referenceOptLevel
  let args ← arguments.mapM (fun binding => rustArgument target architecture false binding referenceOptLevel)
  return {
    arguments := args
    returnValue := ret
    callingConvention := ⟨.rust, none, none, none⟩
    canUnwind := rustCanUnwind unwind
    cVariadic := false
    fixedCount := arguments.size
  }

/-- Document-owned counterpart: dyn layout evidence and optimizer flags are
validated by the mode query, not supplied as ABI answers. -/
def rustFunctionAbiComponentOfDocument (d : Document) (unwind : RustUnwindFacts)
    (arguments : Array AbiTypeBinding) (result : AbiTypeBinding) : Except String Input.FunctionAbi := do
  let argument (isReturn : Bool) (binding : AbiTypeBinding) : Except String Input.AbiArgument := do
    return ⟨binding.typeId, binding.layoutId, ← rustPassModeOfDocument d isReturn binding.type⟩
  return {
    arguments := ← arguments.mapM (argument false)
    returnValue := ← argument true result
    callingConvention := ⟨.rust, none, none, none⟩
    canUnwind := rustCanUnwind unwind, cVariadic := false, fixedCount := arguments.size }

end Miri.Frontend.Foundation
