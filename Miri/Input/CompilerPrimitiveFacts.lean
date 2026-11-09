import Miri.Input.RuntimeMetadata

/-! Actual compiler-selected primitive/lang-item/path types. Canonical source
query references establish identity; display spelling or layout equality does
not. In particular Ordering is tcx.ty_ordering_enum, and c_ulong is the source
core::ffi path query, never derived from host or target triple. -/
namespace Miri.Input.CompilerPrimitiveFacts
open Lean Miri.ABI
private def referencedLayout (runtime : RuntimeMetadata) (id : TypeId) :
    Except String (TyAndLayout TypeId) :=
  runtime.lookup id |>.mapError toString

/-- Read one exact compiler primitive query key; no type-name search occurs. -/
def primitiveLayout (runtime : RuntimeMetadata) (key : String) : Except String (TyAndLayout TypeId) := do
  let p := runtime.source.queries.primitives
  let id ← match key with
    | "u8" => pure p.u8 | "u16" => pure p.u16 | "u32" => pure p.u32
    | "u64" => pure p.u64 | "u128" => pure p.u128
    | "i8" => pure p.i8 | "i16" => pure p.i16 | "i32" => pure p.i32
    | "i64" => pure p.i64 | "i128" => pure p.i128 | "bool" => pure p.bool
    | "pointer_tag_integer" => pure p.pointerTagInteger
    | "usize" => pure p.usize | "isize" => pure p.isize | "unit" => pure p.unit
    | "unit_pointer_const" => pure p.unitPointerConst | "unit_pointer_mut" => pure p.unitPointerMut
    | "imm_u8_pointer" => pure p.immU8Pointer | "imm_u8_pointer_pointer" => pure p.immU8PointerPointer
    | "type_name_result_type" => pure p.typeNameResultType
    | _ => throw s!"unknown compiler primitive query {key}"
  referencedLayout runtime id

def namedLayout (runtime : RuntimeMetadata) (key : String) : Except String (TyAndLayout TypeId) := do
  let some entries := runtime.source.queries.namedTypes | throw "compiler named types absent"
  let some (_, id) := entries.find? (·.1 == key) | throw s!"compiler named type absent: {key}"
  referencedLayout runtime id

def orderingLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  let some id := runtime.source.queries.primitives.orderingEnum | throw "compiler Ordering type absent"
  referencedLayout runtime id

def callerLocationType (runtime : RuntimeMetadata) : Except String TypeId := do
  let some id := runtime.source.queries.primitives.callerLocationType | throw "compiler caller location type absent"
  let _ ← runtime.node id |>.mapError toString
  pure id

def cULongLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := namedLayout runtime "c_ulong"
def offTLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := namedLayout runtime "off_t"
def u32Layout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := primitiveLayout runtime "u32"
def usizeLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := primitiveLayout runtime "usize"
def unitLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := primitiveLayout runtime "unit"
def unitPointerConstLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := primitiveLayout runtime "unit_pointer_const"
def unitPointerMutLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := primitiveLayout runtime "unit_pointer_mut"
end Miri.Input.CompilerPrimitiveFacts
