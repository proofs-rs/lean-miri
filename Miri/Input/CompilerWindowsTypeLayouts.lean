import Miri.Input.RuntimeMetadata

/-! Exact source `helpers.rs::windows_ty_layout` queries. Windows shim
aggregates resolve only through rustc's `std::sys::pal::windows::c` TypeNS
catalog; neither target spelling nor layout coincidence is used as a fallback.
-/
namespace Miri.Input.CompilerWindowsTypeLayouts
open Lean Miri.ABI

def layout (runtime : RuntimeMetadata) (name : String) : Except String (TyAndLayout TypeId) := do
  let some catalog := runtime.source.queries.windowsTypeLayouts | throw "compiler Windows type catalog absent"
  unless catalog.cratePath == #["std", "sys", "pal", "windows", "c"] do
    throw "compiler Windows type query has wrong canonical crate path"
  unless catalog.namespaceName == "TypeNS" do
    throw "compiler Windows type query has wrong namespace"
  let some (_, id) := catalog.entries.find? (·.1 == name) | throw s!"compiler Windows type absent: {name}"
  runtime.lookup id |>.mapError toString
end Miri.Input.CompilerWindowsTypeLayouts
