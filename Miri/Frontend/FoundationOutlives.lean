import Miri.Frontend.Foundation

/-! A deliberately small type-outlives query from structural finite material.
Pinned rustc_type_ir::outlives::push_outlives_components emits no lifetime
components for scalar leaves, recurses through arrays/tuples and adds the
referenced lifetime for references. Only component-free scalar/array/unit
material is accepted here; pointer/function signatures and unknown lifetimes
remain unsupported rather than assigning 'static to erased regions. -/
namespace Miri.Frontend.Foundation

/-- A sufficient component-free structural domain for `T: 'static`. This is
not a general region or outlives solver. -/
def checkStaticOutlives (ty : ConcreteType) (region : String) : Except String Unit := do
  unless region == "static" do throw "unsupported type-outlives region"
  go 1024 ty
where
  go (fuel : Nat) (ty : ConcreteType) : Except String Unit := do
    let .succ fuel := fuel | throw "type-outlives structural traversal exhausted"
    match ty with
    | .primitive "bool" "" | .primitive "char" "" => pure ()
    | .primitive "uint" name =>
      unless #["u8", "u16", "u32", "u64", "u128", "usize"].contains name do
        throw "type-outlives unsigned leaf unsupported"
    | .primitive "int" name =>
      unless #["i8", "i16", "i32", "i64", "i128", "isize"].contains name do
        throw "type-outlives signed leaf unsupported"
    | .array element _ => go fuel element
    | .tuple fields =>
      unless fields.isEmpty do throw "type-outlives nonempty tuple unsupported"
    | _ => throw "type-outlives shape or lifetime material unsupported"

end Miri.Frontend.Foundation
