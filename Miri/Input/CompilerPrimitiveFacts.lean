import Miri.Input.RuntimeMetadata

/-! Exact compiler-selected type identities, decoded at the input boundary.
Display names and layout equality never establish identity. -/
namespace Miri.Input.CompilerPrimitiveFacts
open Miri.ABI

def primitiveType (runtime : RuntimeMetadata) (key : String) : Except String TypeId :=
  CompilerTypeCatalogs.lookup runtime.source.compilerTypeCatalogs.primitives key

/-- One exact compiler primitive query; no type-name search occurs. -/
def primitiveLayout (runtime : RuntimeMetadata) (key : String) : Except String (TyAndLayout TypeId) := do
  runtime.lookup (← primitiveType runtime key) |>.mapError toString

def namedLayout (runtime : RuntimeMetadata) (key : String) : Except String (TyAndLayout TypeId) := do
  let id ← CompilerTypeCatalogs.lookup runtime.source.compilerTypeCatalogs.named key
  runtime.lookup id |>.mapError toString

def orderingLayout (runtime : RuntimeMetadata) : Except String (TyAndLayout TypeId) := do
  let id ← CompilerTypeCatalogs.lookup runtime.source.compilerTypeCatalogs.primitiveQueries "ordering_enum"
  runtime.lookup id |>.mapError toString

/-- Exact tcx.caller_location_ty(), preserving canonical compiler identity. -/
def callerLocationType (runtime : RuntimeMetadata) : Except String TypeId := do
  let id ← CompilerTypeCatalogs.lookup runtime.source.compilerTypeCatalogs.primitiveQueries "caller_location_type"
  let _ ← runtime.node id |>.mapError toString
  pure id

def cULongLayout (runtime : RuntimeMetadata) := namedLayout runtime "c_ulong"
def offTLayout (runtime : RuntimeMetadata) := namedLayout runtime "off_t"
def u32Layout (runtime : RuntimeMetadata) := primitiveLayout runtime "u32"
def usizeLayout (runtime : RuntimeMetadata) := primitiveLayout runtime "usize"
def unitLayout (runtime : RuntimeMetadata) := primitiveLayout runtime "unit"
def unitPointerConstLayout (runtime : RuntimeMetadata) := primitiveLayout runtime "unit_pointer_const"
def unitPointerMutLayout (runtime : RuntimeMetadata) := primitiveLayout runtime "unit_pointer_mut"
end Miri.Input.CompilerPrimitiveFacts
