import Miri.Frontend.FoundationLayout
import Miri.Frontend.FoundationPhysicalTypes

/-! Demand-time components of the pinned Rust ABI algorithm.

Sources: rustc_target/src/callconv/mod.rs::{ArgAbi::new,adjust_for_rust_abi}
and rustc_middle/src/ty/layout.rs::fn_can_unwind, revision
8144389c895da997dbdecaa635e41d6a50be6ffd. These components do not construct
`Input.FunctionAbi`: mode shapes omit attributes and physical layout identities.
The architecture and unwind facts below must come from finite compiler source
material; they must not be inferred from the host or the target triple. -/
namespace Miri.Frontend.Foundation

/-- Source/session facts consumed by `fn_can_unwind` for an ordinary Rust-ABI
instance. Foreign-item and drop-glue facts are retained even though ordinary
Rust definitions normally make these branches trivial. -/
structure RustUnwindFacts where
  hasDefinition : Bool
  neverUnwind : Bool
  panicUnwinds : Bool
  foreignItem : Bool
  panicInDropUnwinds : Bool
  dropGlue : Bool
  deriving Repr, DecidableEq

/-- The Rust-family branch of the pinned `fn_can_unwind` algorithm. This does
not compute definition attributes or establish that supplied facts are genuine. -/
def rustCanUnwind (facts : RustUnwindFacts) : Bool :=
  if facts.hasDefinition && (facts.neverUnwind ||
      (!facts.panicUnwinds && !facts.foreignItem) ||
      (!facts.panicInDropUnwinds && facts.dropGlue)) then false
  else facts.panicUnwinds

theorem rustCanUnwind_panicAbort (facts : RustUnwindFacts)
    (h : facts.panicUnwinds = false) : rustCanUnwind facts = false := by
  simp [rustCanUnwind, h]

theorem rustCanUnwind_noDefinition (facts : RustUnwindFacts)
    (h : facts.hasDefinition = false) : rustCanUnwind facts = facts.panicUnwinds := by
  simp [rustCanUnwind, h]

/-- Read only finite source/session facts, never a precomputed unwind answer.
The caller supplies the requested body's source row from the same document. -/
def rustUnwindFactsOfSource (source body : Lean.Json) : Except String RustUnwindFacts := do
  let compilation ← source.getObjVal? "compilation"
  let strategy ← compilation.getObjValAs? String "panic_strategy"
  let dropStrategy ← compilation.getObjValAs? String "panic_in_drop"
  unless (strategy == "unwind" || strategy == "abort") &&
      (dropStrategy == "unwind" || dropStrategy == "abort") do
    throw "invalid foundation panic strategy"
  let attrs ← body.getObjVal? "function_attributes"
  return {
    hasDefinition := true
    neverUnwind := ← attrs.getObjValAs? Bool "never_unwind"
    panicUnwinds := strategy == "unwind"
    foreignItem := ← attrs.getObjValAs? Bool "is_foreign"
    panicInDropUnwinds := dropStrategy == "unwind"
    dropGlue := ← attrs.getObjValAs? Bool "is_drop_glue"
  }

/-- A projection of pass modes, deliberately excluding optimization attributes,
cast noundef, address spaces and physical layout IDs. It cannot be used as a
replacement for genuine interpreter `FnAbi` evidence. -/
inductive RustModeShape where
  | ignore
  | direct (zeroExtendBool : Bool)
  | pair
  | integerCast (sizeBytes : Nat)
  | indirect
  deriving Repr, DecidableEq

/-- Supported scalar, array and pointer Rust ABI mode shapes on x86_64.
The architecture-specific pre-adjustment is empty on this architecture. Shared
str references have scalar-pair shape; their attributes remain separately guarded
by source optimization/position facts. Floats, mutable references, nonempty
tuples, foreign ABIs and other architectures fail closed.
`layoutOf` supplies the supported scalar/array size checks before classification.
No complete FnAbi or attribute equivalence is claimed. -/
private def rustModeCore (target : Target) (architecture : String)
    (isReturn : Bool) (ty : ConcreteType)
    (query : ConcreteType → Except String FoundationLayout) : Except String RustModeShape := do
  unless architecture == "x86_64" do
    throw "foundation Rust ABI mode shape requires explicit x86_64 architecture"
  unless target.pointerSizeBits == 64 do
    throw "foundation x86_64 Rust ABI requires 64-bit pointers"
  if let .primitive "str" "" := ty then
    throw "unsized str Rust ABI mode shape is unsupported"
  if let .dynamicObject _ := ty then
    throw "unsized dynamic object Rust ABI mode shape is unsupported"
  let layout ← query ty
  if layout.size == 0 then return .ignore
  match ty with
  | .closure _ _ => throw "closure ABI requires full physical classification"
  | .nominal _ _ => throw "nominal component requires document physical query"
  | .patternNotNull _ => throw "general constrained-pattern Rust ABI unsupported"
  | .primitive kind _ => return .direct (kind == "bool")
  | .array _ _ =>
    if isReturn && layout.size > 2 * (target.pointerSizeBits / 8) then return .indirect
    if layout.size <= target.pointerSizeBits / 8 then return .integerCast layout.size
    return .indirect
  | .tuple _ => throw "nonzero tuple Rust ABI mode shape is unsupported"
  | .pointer kind pointee =>
    let info ← pointerKindInfo kind
    if info.region.isSome && info.mutability != .Not then
      throw "mutable-reference Rust ABI attributes are unsupported"
    match pointee with
    | .primitive "str" "" | .dynamicObject _ =>
      unless info.region.isSome do throw "wide raw-pointer Rust ABI mode shape is unsupported"
      return .pair
    | _ => pure ()
    return .direct false
  | .dynamicObject _ => throw "dynamic object ABI mode unsupported"
  | .functionPointer .. => return .direct false

/-- Target-only mode queries cannot assert unavailable dyn declaration evidence. -/
def rustModeShape (target : Target) (architecture : String) (isReturn : Bool)
    (ty : ConcreteType) : Except String RustModeShape :=
  rustModeCore target architecture isReturn ty (layoutOf target)

/-- ABI layout context from the same checked pure physical construction used
by the document registry, including supported nominal declarations. -/
def rustAbiLayoutOfDocument (d : Document) (ty : ConcreteType) : Except String FoundationLayout := do
  let row ← physicalLayoutOfDocument d ty
  let some size := row.sizeBytes | throw "ABI physical size absent"
  let some align := row.abiAlignBytes | throw "ABI physical alignment absent"
  return ⟨size,align⟩

def rustModeShapeOfDocument (d : Document) (isReturn : Bool) (ty : ConcreteType) : Except String RustModeShape := do
  if let .nominal .. := ty then
    unless d.target.architecture == "x86_64" && d.target.pointerSizeBits == 64 do
      throw "nominal Rust ABI requires explicit x86_64 target"
    let row ← physicalLayoutOfDocument d ty
    if row.sizeBytes == some 0 then return .ignore
    let some backend := row.backendRepresentation | throw "nominal backend absent"
    let some scalar := backend.scalar | throw "nominal Rust ABI requires integer scalar"
    unless backend.kind == .scalar && scalar.kind == .initialized &&
        scalar.primitive.kind == .integer && scalar.validRange.isSome do
      throw "nominal pointer/aggregate Rust ABI unsupported"
    -- arg_attrs_for_rust_scalar returns NoUndef immediately for initialized
    -- integers; adjust_for_rust_abi tests scalar validity, not nominal TyKind,
    -- when applying bool zero-extension. No pointee/trait facts are needed.
    return .direct (scalar.primitive.sizeBytes == 1 && scalar.primitive.signed == some false &&
      scalar.validRange == some (0,1))
  rustModeCore d.target d.target.architecture isReturn ty (rustAbiLayoutOfDocument d)

end Miri.Frontend.Foundation
