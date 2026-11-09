import Miri.Input.RuntimeMetadata

/-! Actual compiler-selected primitive/lang-item/path types. Canonical source
query references establish identity; display spelling or layout equality does
not. In particular Ordering is tcx.ty_ordering_enum, and c_ulong is the source
core::ffi path query, never derived from host or target triple. -/
namespace Miri.Input.CompilerPrimitiveFacts
open Lean Miri.ABI
private def referencedLayout (runtime : RuntimeMetadata) (j : Json) :
    Except String (TyAndLayout TypeId) := do
  let id ← j.getNat?
  runtime.lookup id |>.mapError toString
private def primitives (runtime : RuntimeMetadata) : Except String Json :=
  runtime.source.raw.getObjVal? "compiler_runtime_primitives"
/-- Read one exact compiler primitive query key; no type-name search occurs. -/
def primitiveLayout (runtime : RuntimeMetadata) (key : String) : Except String (TyAndLayout TypeId) := do
  referencedLayout runtime (← (← primitives runtime).getObjVal? key)

/-- Read one exact source path/constructor query key from the named catalog. -/
def namedLayout (runtime : RuntimeMetadata) (key : String) : Except String (TyAndLayout TypeId) := do
  let entries ← runtime.source.raw.getObjVal? "compiler_named_types"
  referencedLayout runtime (← entries.getObjVal? key)

def orderingLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  referencedLayout runtime (← (← primitives runtime).getObjVal? "ordering_enum")

/-- Exact tcx.caller_location_ty(): &'static Location<'static>, preserving
both source reference/lifetime construction and canonical compiler identity. -/
def callerLocationType (runtime : RuntimeMetadata) : Except String TypeId := do
  let value ← (← primitives runtime).getObjVal? "caller_location_type"
  let id ← value.getNat?
  let _ ← runtime.node id |>.mapError toString
  pure id

def cULongLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  let entries ← runtime.source.raw.getObjVal? "compiler_named_types"
  referencedLayout runtime (← entries.getObjVal? "c_ulong")

def offTLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  let entries ← runtime.source.raw.getObjVal? "compiler_named_types"
  referencedLayout runtime (← entries.getObjVal? "off_t")

def u32Layout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  referencedLayout runtime (← (← primitives runtime).getObjVal? "u32")

def usizeLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  referencedLayout runtime (← (← primitives runtime).getObjVal? "usize")

def unitLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  referencedLayout runtime (← (← primitives runtime).getObjVal? "unit")

def unitPointerConstLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  referencedLayout runtime (← (← primitives runtime).getObjVal? "unit_pointer_const")

def unitPointerMutLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  referencedLayout runtime (← (← primitives runtime).getObjVal? "unit_pointer_mut")
end Miri.Input.CompilerPrimitiveFacts
