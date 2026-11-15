import Miri.Frontend.FoundationRegionErasure
import Miri.Input.Model

/-! Only structural compiler leaves for dyn objects. Pinned ty/util.rs marks
dynamic objects always-needs-drop for synchronous drop; inhabitedness treats
them inhabited. Freeze/Unpin/UnsafeUnpin require trait resolution and are absent.
The nominal DynMetadata type query and vtable/field metadata likewise remain
absent rather than inventing a pointer-sized nominal type or method table. -/
namespace Miri.Frontend.Foundation

def dynamicCompilerFacts (ty : ConcreteType) (_self normalized u8 : Nat) :
    Except String Input.TypeCompilerFacts := do
  let .dynamicObject _ := ty | throw "structural dynamic facts require dynamic source"
  let erasable ← hasErasableRegions ty
  return {
    typingEnvironment := "fully_monomorphized"
    booleanQueries := #[
      ("is_unsafe_cell", false), ("has_erasable_regions", erasable),
      ("is_c_void", false), ("is_simd", false), ("is_box", false),
      ("is_global_box", false), ("is_dynamic", true), ("is_too_generic", false),
      ("is_monomorphic", true), ("is_monomorphic_enough", true),
      ("is_like_maybe_dangling", false), ("needs_drop", true),
      ("opsem_inhabited", true), ("is_sized", false)]
    typeQueries := #[
      ("normalized", some normalized), ("metadata_tail", some normalized),
      ("discriminant_type", some u8), ("builtin_deref_explicit", none),
      ("builtin_deref_implicit", none), ("boxed_type", none), ("unsafe_binder_erased", none)]
    discriminants := some ⟨false, none, #[]⟩ }

end Miri.Frontend.Foundation
