import Miri.Frontend.FoundationPhysicalRegistry

/-! Exact structural primitive-query identities used by the fixed interpreter.
Pinned exporter main.rs RuntimePrimitives mirrors tcx.types, Ty::new_imm_ptr,
Ty::new_mut_ptr and Ty::new_imm_ref(Erased,str). The pointer tag integer follows
rustc_abi::TargetDataLayout::ptr_sized_integer, using pointer offset width.
Optional nominal lang-item queries remain absent evidence, so their consumers
fail closed. This is not a catalog of source lang items or runtime readiness. -/
namespace Miri.Frontend.Foundation

/-- Populate all mandatory structural primitive references without arbitrary
IDs. Unsupported physical shapes/target widths propagate as errors. -/
def physicalPrimitiveCatalog (initial : PhysicalTypeRegistry) :
    Except String (PhysicalTypeRegistry × Input.Catalog.Primitives) := do
  let (r, unsigned, signed) ← seed initial
  let target ← runtimeTargetOfTarget r.registry.document.target

  let offsetBits := target.pointerOffset.bytes.toNat * 8
  unless offsetBits == target.base.pointerWidth.bits.toNat do
    throw "primitive catalog requires equal stored-pointer and pointer-offset widths"
  unless #[16, 32, 64].contains offsetBits do throw "unsupported pointer tag integer width"
  let (r, pointerTagInteger) ← r.intern (.primitive "uint" s!"u{offsetBits}")
  let (r, boolean) ← r.intern (.primitive "bool" "")
  let (r, usize) ← r.intern (.primitive "uint" "usize")
  let (r, isize) ← r.intern (.primitive "int" "isize")
  let unitType := ConcreteType.tuple #[]
  let byte := ConcreteType.primitive "uint" "u8"
  let bytePtr := ConcreteType.pointer "raw_pointer_const" byte
  let (r, unit) ← r.intern unitType
  let (r, unitPointerConst) ← r.intern (.pointer "raw_pointer_const" unitType)
  let (r, unitPointerMut) ← r.intern (.pointer "raw_pointer_mut" unitType)
  let (r, immU8Pointer) ← r.intern bytePtr
  let (r, immU8PointerPointer) ← r.intern (.pointer "raw_pointer_const" bytePtr)
  let (r, typeNameResultType) ← r.intern (.pointer "reference_erased_const" (.primitive "str" ""))
  let get (ids : Array Nat) (i : Nat) : Except String Nat :=
    match ids[i]? with
    | some id => pure id
    | none => throw "primitive integer identity absent"
  return (r, {
    u8 := ← get unsigned 0, u16 := ← get unsigned 1, u32 := ← get unsigned 2,
    u64 := ← get unsigned 3, u128 := ← get unsigned 4,
    i8 := ← get signed 0, i16 := ← get signed 1, i32 := ← get signed 2,
    i64 := ← get signed 3, i128 := ← get signed 4,
    bool := boolean, pointerTagInteger, usize, isize, unit, unitPointerConst,
    unitPointerMut, immU8Pointer, immU8PointerPointer, typeNameResultType,
    callerLocationType := none, orderingEnum := none })

where
  seed (initial : PhysicalTypeRegistry) : Except String (PhysicalTypeRegistry × Array Nat × Array Nat) := do
    let mut r := initial
    let mut unsigned := #[]
    let mut signed := #[]
    for width in #[8, 16, 32, 64, 128] do
      let (next, id) ← r.intern (.primitive "uint" s!"u{width}")
      r := next
      unsigned := unsigned.push id
      let (next, id) ← r.intern (.primitive "int" s!"i{width}")
      r := next
      signed := signed.push id
    return (r, unsigned, signed)

end Miri.Frontend.Foundation
