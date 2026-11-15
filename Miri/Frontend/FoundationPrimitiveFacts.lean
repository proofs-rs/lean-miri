import Miri.Frontend.FoundationPhysicalRegistry
import Miri.Frontend.FoundationRegionErasure
import Miri.Frontend.FoundationDynamicFacts

/-! Compiler leaves for the closed physical subset, computed from structure.
Pinned rustc sources: ty/util.rs::{is_trivially_freeze,is_trivially_unpin,
needs_drop_components_with_async,struct_tail_raw}; ty/sty.rs::{builtin_deref,
discriminant_ty,ptr_metadata_ty_or_tail,is_like_maybe_dangling};
ty/inhabitedness/mod.rs::OpSemInhabitedness::is_inhabited_ty.
Primitive/reference leaves are inhabited, Freeze and both Unpin traits. str
is unsized with canonical usize metadata; the other primitive shapes are Sized.
Dyn objects use the separate partial DynamicFacts bag: unresolved solver and
nominal metadata queries remain absent.
Arrays, shared references and pointer signatures recurse; the only supported
tuple is empty. No trait solver fallback is taken. Static/Erased region flags
and erasure are computed structurally; parameter/inference flags are absent.
Hashing, nominal definitions and projection catalogs are intentionally absent. -/
namespace Miri.Frontend.Foundation

/-- Check the entire supported domain before assigning any compiler answer. -/
def primitiveFactsDomain (ty : ConcreteType) : Except String Unit := go 1024 ty
where
  go (fuel : Nat) (ty : ConcreteType) : Except String Unit := do
    let .succ fuel := fuel | throw "primitive compiler facts recursion exhausted"
    match ty with
    | .primitive "bool" "" | .primitive "char" "" | .primitive "str" "" => pure ()
    | .primitive "int" name =>
      unless #["i8", "i16", "i32", "i64", "i128", "isize"].contains name do
        throw "unsupported signed compiler facts"
    | .primitive "uint" name =>
      unless #["u8", "u16", "u32", "u64", "u128", "usize"].contains name do
        throw "unsupported unsigned compiler facts"
    | .array (.primitive "str" "") _ | .array (.dynamicObject _) _ =>
      throw "unsized array compiler facts unsupported"
    | .array element _ => go fuel element
    | .pointer kind pointee =>
      let info ← pointerKindInfo kind
      if info.region.isSome && info.mutability != .Not then
        throw "mutable-reference compiler facts unsupported"
      go fuel pointee
    | .functionPointer inputs output safety abi variadic =>
      unless (safety == "safe" || safety == "unsafe") && abi == "rust" && !variadic do
        throw "function-pointer compiler signature unsupported"
      for input in inputs do go fuel input
      go fuel output
    | .dynamicObject source =>
      for ty in source.arguments do go fuel ty
      for projection in source.projections do
        for ty in projection.arguments do go fuel ty
        go fuel projection.term
    | .tuple fields =>
      unless fields.isEmpty do throw "nonempty tuple compiler facts unsupported"
    | _ => throw "unsupported primitive compiler facts"

/-- IDs must be provided by the physical registry: self, unit metadata, and u8
(the pinned discriminant type for every supported non-enum shape). -/
def primitiveCompilerFacts (ty : ConcreteType) (self unit u8 : Nat)
    (rawPointee : Option Nat := none) (normalized : Option Nat := none)
    (usize : Option Nat := none) :
    Except String Input.TypeCompilerFacts := do
  primitiveFactsDomain ty
  let isStr := match ty with | .primitive "str" "" => true | _ => false
  let metadata ← if isStr then do
      let some id := usize | throw "str compiler fact lacks canonical usize identity"
      pure id
    else pure unit
  let erasable ← hasErasableRegions ty
  let normalized ← if erasable then do
      let some id := normalized | throw "reference compiler fact lacks erased type identity"
      pure id
    else pure self
  if let .dynamicObject _ := ty then return ← dynamicCompilerFacts ty self normalized u8
  let explicitDeref ← match ty with
    | .pointer .. => do
      let some pointee := rawPointee | throw "pointer compiler fact lacks physical pointee"
      pure (some pointee)
    | _ => pure none
  let implicitDeref ← match ty with
    | .pointer kind _ => do
      let info ← pointerKindInfo kind
      pure (if info.region.isSome then explicitDeref else none)
    | _ => pure none
  return {
    typingEnvironment := "fully_monomorphized"
    booleanQueries := #[
      ("is_unsafe_cell", false), ("has_erasable_regions", erasable),
      ("is_c_void", false), ("is_simd", false), ("is_box", false),
      ("is_global_box", false), ("is_dynamic", false), ("is_too_generic", false),
      ("is_monomorphic", true), ("is_monomorphic_enough", true),
      ("is_like_maybe_dangling", false), ("is_freeze", true),
      ("is_unpin", true), ("is_unsafe_unpin", true), ("needs_drop", false),
      ("opsem_inhabited", true), ("is_sized", !isStr)]
    typeQueries := #[
      ("normalized", some normalized), ("metadata_tail", some normalized),
      ("pointer_metadata_type", some metadata), ("discriminant_type", some u8),
      ("builtin_deref_explicit", explicitDeref), ("builtin_deref_implicit", implicitDeref),
      ("boxed_type", none), ("unsafe_binder_erased", none)]
    discriminants := some ⟨false, none, #[]⟩ }

namespace PhysicalTypeRegistry

/-- Attach derived leaves to explicitly demanded supported rows. Other rows
retain their existing evidence, including absent facts for unsupported auxiliary
material. Each selected row must pass primitiveFactsDomain. The
additional demands are exact unit/u8 result types, usize when str is selected,
and supported region-erased identities. -/
def withPrimitiveFactsFor (r : PhysicalTypeRegistry) (typeIds : Array Nat) : Except String PhysicalTypeRegistry := do
  let (r, unit) ← r.intern (.tuple #[])
  let (r, u8) ← r.intern (.primitive "uint" "u8")
  let needsUsize := typeIds.any fun id => match r.registry.entries[id]? with
    | some entry => match entry.type with | .primitive "str" "" => true | _ => false
    | none => false
  let (r, usize) ← if needsUsize then do
      let (r, id) ← r.intern (.primitive "uint" "usize")
      pure (r, some id)
    else pure (r, none)
  let roots := typeIds ++ #[unit, u8] ++ (match usize with | some id => #[id] | none => #[])
  let originalCount := r.types.size
  let mut registry := r
  let mut normalization := #[]
  for i in roots do
    let some entry := registry.registry.entries[i]? | throw "compiler fact source identity absent"
    primitiveFactsDomain entry.type
    let (next, normalized) ← registry.intern (← eraseRegions entry.type)
    registry := next
    normalization := normalization.push (i, normalized)
  let r := registry
  let additional := (List.range (r.types.size - originalCount)).toArray.map (· + originalCount)
  let mut nodes := r.types
  for i in roots ++ additional do
    let some entry := r.registry.entries[i]? | throw "compiler fact type identity absent"
    let (node, _) ← r.lookup i
    let rawPointee := match node.shape with
      | .rawPointer pointee _ | .reference pointee _ _ => some pointee
      | _ => none
    let normalized := (normalization.find? (·.1 == i)).map (·.2)
    let facts ← primitiveCompilerFacts entry.type i unit u8 rawPointee normalized usize
    if h : i < nodes.size then
      nodes := nodes.set i { node with compilerFacts := some facts }
    else
      throw "compiler fact destination identity absent"
  return { r with types := nodes }

/-- Attach supported compiler leaves to the entire current physical domain.
Unlike withPrimitiveFactsFor, this rejects any unsupported current row. -/
def withPrimitiveFacts (r : PhysicalTypeRegistry) : Except String PhysicalTypeRegistry := do
  r.withPrimitiveFactsFor (List.range r.types.size).toArray

end PhysicalTypeRegistry
end Miri.Frontend.Foundation
