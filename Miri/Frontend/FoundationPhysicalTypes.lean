import Miri.Frontend.FoundationLayout
import Miri.Frontend.FoundationNominalRules

/-! Physical rows computed from finite target material. The constructors follow
pinned rustc_abi/layout/simple.rs::scalar and layout.rs::layout_of_array_like.
Empty tuples use layout_of_univariant_biased with no fields and default repr:
rustc_ty_utils/src/layout.rs::layout_of_uncached maps tuples to univariant;
its empty-field alignment is aggregate_align and its seed is zero.
Thin pointer layout follows rustc_ty_utils/src/layout.rs's Ref/RawPtr branch:
Primitive::Pointer(AddressSpace::ZERO), a full raw range or reference start 1.
These are representation facts and supply no dereferenceability, allocation,
provenance or borrow permission evidence.
Dyn objects use unit(false). Dyn-pointer metadata is a nonnull AS0 vtable
scalar only after validating the finite DynMetadata/NonNull/PhantomData source
chain. Scalar-pair niche selection follows layout/simple.rs (data wins ties).
They supply no vtable allocation, nominal metadata type or method table. -/
namespace Miri.Frontend.Foundation

private def memoryBackend : Input.BackendRepr :=
  ⟨.memory, some true, none, none, none, none, none, none, none⟩

private def singleVariant : Input.VariantsLayout :=
  ⟨.single, some 0, none, none, none, #[]⟩

private def baseLayout (size align seed : Nat) (fields : Input.FieldShape)
    (offsets : Input.LayoutFieldOffsets) (backend : Input.BackendRepr)
    (niche : Option Input.NicheLayout) : Input.Layout := {
  maxReprAlignBytes := none, reprC := false, uninhabited := false,
  largestNiche := niche, randomizationSeed := seed, kind := .layout,
  sizeBytes := some size, abiAlignBytes := some align,
  unadjustedAbiAlignBytes := some align, fieldOffsetsBytes := offsets,
  fields := some fields, variantsLayout := some singleVariant,
  backendRepresentation := some backend, variantsKind := some .single,
  backendReprKind := some backend.kind, variants := none, backendRepr := none }

/-- Structural primitive tags preserve pointer-sized type identity while the
physical primitive tag is always a fixed-width integer, as required by the
existing runtime converter. -/
def physicalIntegerKind (name : String) : Except String MIR.IntegerKind :=
  match name with
  | "i8" => pure .i8 | "u8" => pure .u8
  | "i16" => pure .i16 | "u16" => pure .u16
  | "i32" => pure .i32 | "u32" => pure .u32
  | "i64" => pure .i64 | "u64" => pure .u64
  | "i128" => pure .i128 | "u128" => pure .u128
  | "isize" => pure .isize | "usize" => pure .usize
  | _ => throw "unsupported physical integer tag"

private def scalarLayout (size align : Nat) (signed : Bool) (last : Nat) :
    Except String Input.Layout := do
  let tag ← physicalIntegerKind s!"{if signed then "i" else "u"}{size * 8}"
  let primitive : Input.PrimitiveLayout :=
    ⟨.integer, size, some (.known tag), some signed, none, none⟩
  let scalar : Input.ScalarLayout := ⟨.initialized, primitive, some (0, last)⟩
  let niche := if last == 2 ^ (size * 8) - 1 then none
    else some (Input.NicheLayout.mk 0 primitive (0, last))
  let rotated := UInt64.ofNat ((last % 2^64) / 2^16 + (last % 2^16) * 2^48)
  let seed := (UInt64.ofNat size + UInt64.ofNat ((if signed then 1 else 2) * 2^32) + rotated).toNat
  return baseLayout size align seed ⟨.primitive, 0, none, none, #[], #[]⟩
    (.explicit #[]) ⟨.scalar, none, some scalar, none, none, none, none, none, none⟩ niche

/-- Exact supported physical layouts; unsupported shapes and missing complete
material remain errors. Recursion and object bounds use the same checked query
as size/alignment construction. No rustc process or answer cache is consulted. -/
private def physicalLayoutCore (target : ABI.RuntimeTargetDataLayout)
    (query : ConcreteType → Except String FoundationLayout) (ty : ConcreteType) :
    Except String Input.Layout := do
  let _ ← query ty
  go 1024 ty
where
  go (fuel : Nat) (ty : ConcreteType) : Except String Input.Layout := do
    let .succ fuel := fuel | throw "physical layout recursion exhausted"
    let basic ← query ty
    match ty with
    | .closure _ arguments =>
      let some (.tuple fields) := arguments.back? | throw "closure upvars tuple absent"
      unless arguments.size ≥ 3 do throw "closure synthetic arguments absent"
      if fields.size > 1 then
        return ← scalarAggregateLayout target (← fields.mapM (go fuel)) false
      let layout ← go fuel (.tuple fields)
      if fields.isEmpty then return layout
      let some field := fields[0]? | throw "closure field absent"
      unless fields.size == 1 do throw "multiple closure upvars unsupported"
      let child ← go fuel field
      return { layout with randomizationSeed := child.randomizationSeed }
    | .nominal _ _ => throw "nominal layout requires document material"
    | .patternNotNull _ => throw "general constrained-pattern physical layout unsupported"
    | .primitive "str" "" =>
      return baseLayout 0 basic.align 0xc1325f37d127be22
        ⟨.array, 0, none, some 1, #[], #[]⟩ (.arrayFormula 1 0)
        { memoryBackend with sized := some false } none
    | .primitive kind _name =>
      let signed := kind == "int"
      let last := if kind == "bool" then 1 else if kind == "char" then 0x10ffff
        else 2 ^ (basic.size * 8) - 1
      scalarLayout basic.size basic.align signed last
    | .array element count =>
      let elem ← go fuel element
      let some stride := elem.sizeBytes | throw "physical element size absent"
      let seed := (UInt64.ofNat elem.randomizationSeed + UInt64.ofNat count).toNat
      return baseLayout basic.size basic.align seed
        ⟨.array, count, none, some stride, #[], #[]⟩ (.arrayFormula stride count)
        memoryBackend (if count == 0 then none else elem.largestNiche)
    | .tuple elements =>
      if elements.isEmpty then
        let align ← target.aggregateAlign.bytes.mapError toString
        return baseLayout 0 align.toNat 0 ⟨.arbitrary, 0, none, none, #[], #[]⟩
          (.explicit #[]) memoryBackend none
      if elements.size > 1 then
        return ← scalarAggregateLayout target (← elements.mapM (go fuel)) true
      let some field := elements[0]? | throw "singleton tuple field absent"
      let child ← go fuel field
      let some backend := child.backendRepresentation | throw "singleton tuple backend absent"
      unless backend.kind == .scalar && child.sizeBytes != some 0 &&
          child.abiAlignBytes == some basic.align do
        throw "singleton tuple requires filling scalar field"
      -- Default repr, one field: offset0, identity memory order; scalar
      -- newtype optimization and seed sum preserve the child's backend/niche.
      return { child with
        fields := some ⟨.arbitrary, 1, none, none, #[0], #[0]⟩
        fieldOffsetsBytes := .explicit #[0]
        -- MaybeUnsized excludes the sole tail from the field seed sum.
        randomizationSeed := 0 }
    | .dynamicObject _ =>
      return baseLayout 0 basic.align 0 ⟨.arbitrary, 0, none, none, #[], #[]⟩
        (.explicit #[]) {memoryBackend with sized := some false} none
    | .functionPointer .. =>
      -- rustc_ty_utils::layout_of_uncached uses the instruction address space
      -- and excludes null, independent of the source signature.
      let primitive : Input.PrimitiveLayout :=
        ⟨.pointer, basic.size, none, none, none, some target.instructionAddressSpace.value.toNat⟩
      let last := 2 ^ (basic.size * 8) - 1
      let scalar : Input.ScalarLayout := ⟨.initialized, primitive, some (1, last)⟩
      let rotate (n : Nat) := UInt64.ofNat ((n % 2^64) / 2^16 + (n % 2^16) * 2^48)
      let seed := (UInt64.ofNat basic.size + UInt64.ofNat (4 * 2^32) + rotate 1 + rotate last).toNat
      return baseLayout basic.size basic.align seed ⟨.primitive, 0, none, none, #[], #[]⟩
        (.explicit #[]) ⟨.scalar, none, some scalar, none, none, none, none, none, none⟩
        (some (Input.NicheLayout.mk 0 primitive (1, last)))
    | .pointer kind pointee =>
      let info ← pointerKindInfo kind
      let first := if info.region.isSome then 1 else 0
      let last := 2 ^ (basic.size * 8) - 1
      let primitive : Input.PrimitiveLayout :=
        ⟨.pointer, basic.size, none, none, none, some 0⟩
      let scalar : Input.ScalarLayout := ⟨.initialized, primitive, some (first, last)⟩
      let niche := if first == 0 then none else some (Input.NicheLayout.mk 0 primitive (first, last))
      let rotate (n : Nat) := UInt64.ofNat ((n % 2^64) / 2^16 + (n % 2^16) * 2^48)
      let seed := (UInt64.ofNat basic.size + UInt64.ofNat (4 * 2^32) + rotate first + rotate last).toNat
      if let .dynamicObject _ := pointee then
        let pointerSize := (← (target.pointerSizeIn ABI.AddressSpace.ZERO).mapError toString).bytes.toNat
        let last := 2 ^ (pointerSize * 8) - 1
        let primitive := {primitive with sizeBytes := pointerSize}
        let data := {scalar with primitive, validRange := some (first, last)}
        let metadata : Input.ScalarLayout := ⟨.initialized, primitive, some (1, last)⟩
        let nicheOffset := if first == 1 then 0 else pointerSize
        let niche := some (Input.NicheLayout.mk nicheOffset primitive (1, last))
        return baseLayout basic.size basic.align (2 * pointerSize)
          ⟨.arbitrary, 2, none, none, #[0, pointerSize], #[0, 1]⟩ (.explicit #[0, pointerSize])
          ⟨.scalarPair, none, none, some data, some metadata, some pointerSize, none, none, none⟩ niche
      if let .primitive "str" "" := pointee then
        -- Unsized str metadata is the target pointer-offset-sized unsigned integer.
        let metadataSize := target.pointerOffset.bytes.toNat
        let metadata ← scalarLayout metadataSize
          (← layoutOfRuntime target (.primitive "uint" s!"u{metadataSize * 8}")).align
          false (2 ^ (metadataSize * 8) - 1)
        let some metadataScalar := metadata.backendRepresentation >>= (·.scalar)
          | throw "str metadata scalar absent"
        let some metadataAlign := metadata.abiAlignBytes | throw "str metadata alignment absent"
        let pointerSize := (← (target.pointerSizeIn ABI.AddressSpace.ZERO).mapError toString).bytes.toNat
        let offset := (pointerSize + metadataAlign - 1) / metadataAlign * metadataAlign
        -- Reconstruct the data scalar with its own width, not the pair width.
        let last := 2 ^ (pointerSize * 8) - 1
        let primitive := { primitive with sizeBytes := pointerSize }
        let scalar := { scalar with primitive, validRange := some (first, last) }
        let niche := if first == 0 then none else some (Input.NicheLayout.mk 0 primitive (first, last))
        return baseLayout basic.size basic.align (pointerSize + metadataSize)
          ⟨.arbitrary, 2, none, none, #[0, offset], #[0, 1]⟩ (.explicit #[0, offset])
          ⟨.scalarPair, none, none, some scalar, some metadataScalar, some offset, none, none, none⟩ niche
      return baseLayout basic.size basic.align seed ⟨.primitive, 0, none, none, #[], #[]⟩
        (.explicit #[]) ⟨.scalar, none, some scalar, none, none, none, none, none, none⟩ niche

def physicalLayoutOfRuntime (target : ABI.RuntimeTargetDataLayout) (ty : ConcreteType) :
    Except String Input.Layout := physicalLayoutCore target (layoutOfRuntime target) ty

def physicalLayoutOfDocument (d : Document) (ty : ConcreteType) : Except String Input.Layout := do
  let target ← runtimeTargetOfTarget d.target
  nominalPhysicalLayout d (physicalLayoutCore target (layoutOfDocument d)) ty

/-- Build a row from already interned child and length identities. The caller
must bind those IDs in its document-local pools; no compiler facts are invented. -/
def physicalTypeNode (ty : ConcreteType) (id layoutId : Nat)
    (arrayReferences : Option (Nat × Nat) := none)
    (pointeeReference : Option Nat := none)
    (functionReferences : Option (Array Nat × Nat) := none)
    (dynamicReferences : Option (Array Nat × Option Nat) := none)
    (aggregateReferences : Option (Array Nat) := none) : Except String Input.TypeNode := do
  let (shape, display) ← match ty with
    | .primitive "bool" "" => pure (Input.TypeShape.bool, "bool")
    | .primitive "char" "" => pure (Input.TypeShape.char, "char")
    | .primitive "str" "" => pure (Input.TypeShape.str, "str")
    | .primitive "int" name =>
      unless #["i8", "i16", "i32", "i64", "i128", "isize"].contains name do
        throw "invalid signed primitive name"
      pure (.int (.known (← physicalIntegerKind name)), name)
    | .primitive "uint" name =>
      unless #["u8", "u16", "u32", "u64", "u128", "usize"].contains name do
        throw "invalid unsigned primitive name"
      pure (.uint (.known (← physicalIntegerKind name)), name)
    | .array _ count =>
      let some (element, length) := arrayReferences | throw "array pool identities absent"
      pure (.array element length ⟨count, true⟩, s!"foundation-array-{id}")
    | .closure definition arguments =>
      let some args := aggregateReferences | throw "closure argument identities absent"
      let some (.tuple fields) := arguments.back? | throw "closure upvars absent"
      pure (.closure definition (args.map MIR.GenericArg.Type) fields.size, s!"foundation-closure-{id}")
    | .tuple elements =>
      let ids ← match aggregateReferences with
        | some ids => pure ids
        | none => if elements.isEmpty then pure #[] else throw "tuple field identities absent"
      unless ids.size == elements.size do throw "tuple field identity count mismatch"
      pure (.tuple ids, if elements.isEmpty then "()" else s!"foundation-tuple-{id}")
    | .functionPointer _ _ safety abi variadic =>
      unless (abi == "rust" || abi == "rust_call") && !variadic do throw "physical function-pointer ABI unsupported"
      let safety ← match safety with
        | "safe" => pure MIR.Safety.Safe
        | "unsafe" => pure MIR.Safety.Unsafe
        | _ => throw "physical function-pointer safety unsupported"
      let some (inputs, output) := functionReferences | throw "function-pointer signature identities absent"
      let convention := if abi == "rust_call" then ABI.ExternAbi.RustCall else .Rust
      let signature : Input.FunctionSignature := ⟨inputs, output, safety, convention, variadic⟩
      pure (.functionPointer signature #[], s!"foundation-function-pointer-{id}")
    | .dynamicObject source =>
      let some (predicates, principal) := dynamicReferences | throw "dynamic predicate pool identities absent"
      let region ← match source.region with
        | "static" => pure MIR.Region.Static
        | "erased" => pure MIR.Region.Erased
        | _ => throw "unsupported dynamic object region"
      pure (.dynamicTraitObject predicates principal region, s!"foundation-dynamic-{id}")
    | .patternNotNull _ =>
      let some base := pointeeReference | throw "pattern base identity absent"
      pure (.patternType base .notNull, s!"foundation-pattern-{id}")
    | .pointer kind _ =>
      let info ← pointerKindInfo kind
      let some pointee := pointeeReference | throw "pointer pointee identity absent"
      match info.region with
      | none => pure (.rawPointer pointee info.mutability, s!"foundation-pointer-{id}")
      | some region => pure (.reference pointee info.mutability region, s!"foundation-reference-{id}")
    | _ => throw "unsupported physical type shape"
  return { id, layoutId, shape, display }

end Miri.Frontend.Foundation
