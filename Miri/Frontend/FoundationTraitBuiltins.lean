import Miri.Frontend.Foundation

/-! Closed structural conditions used only by local array blanket headers.
Pinned core marker.rs implements Copy for scalar leaves/raw/shared pointers,
explicitly excludes mutable references; core/array/mod.rs requires element Copy.
Unknown types remain errors rather than failed or successful obligations. -/
namespace Miri.Frontend.Foundation

/-- Return the exact Copy condition after validating this small Sized domain.
All admitted types here are Sized and MetaSized, including mutable references.
No ADT, alias, lifetime inference or general trait search is implemented. -/
def localImplCopy (ty : ConcreteType) : Except String Bool := go 1024 ty
where
  go (fuel : Nat) (ty : ConcreteType) : Except String Bool := do
    let .succ fuel := fuel | throw "local impl builtin recursion exhausted"
    match ty with
    | .primitive "bool" "" | .primitive "char" "" => return true
    | .primitive "uint" name =>
      unless #["u8", "u16", "u32", "u64", "u128", "usize"].contains name do
        throw "unsupported local impl unsigned leaf"
      return true
    | .primitive "int" name =>
      unless #["i8", "i16", "i32", "i64", "i128", "isize"].contains name do
        throw "unsupported local impl signed leaf"
      return true
    | .primitive "float" name =>
      unless #["f16", "f32", "f64", "f128"].contains name do
        throw "unsupported local impl float leaf"
      return true
    | .array element _ => go fuel element
    | .tuple fields =>
      let mut copy := true
      for field in fields do
        let fieldCopy ← go fuel field
        copy := copy && fieldCopy
      return copy
    | .pointer kind pointee =>
      let _ ← go fuel pointee
      if #["reference_static_mut", "reference_erased_mut"].contains kind then return false
      unless #["raw_pointer_const", "raw_pointer_mut", "reference_static_const", "reference_erased_const"].contains kind do
        throw "unsupported local impl pointer kind"
      return true
    | _ => throw "unsupported local impl builtin type"

end Miri.Frontend.Foundation
