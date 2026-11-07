import Miri.Input.RuntimeMetadata

/-! Exact source `helpers.rs::windows_ty_layout` queries. The reader validates
std::sys::pal::windows::c TypeNS and the fully monomorphized environment. -/
namespace Miri.Input.CompilerWindowsTypeLayouts
open Miri.ABI

/-- Resolve one exact Windows C type. Unused unavailable queries remain local
obligations instead of becoming startup prerequisites. -/
def layout (runtime : RuntimeMetadata) (name : String) : Except String (TyAndLayout TypeId) := do
  let id ← CompilerTypeCatalogs.lookup runtime.source.compilerTypeCatalogs.windows name
  runtime.lookup id |>.mapError toString

end Miri.Input.CompilerWindowsTypeLayouts
