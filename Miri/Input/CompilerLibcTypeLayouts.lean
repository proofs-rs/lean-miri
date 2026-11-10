import Miri.Input.RuntimeMetadata

/-! Exact `helpers.rs::libc_ty_layout` and `libc_array_ty_layout` path queries.
Names are looked up only in the exported `libc` TypeNS catalog; there is no
target-name fallback or layout-equality search. -/
namespace Miri.Input.CompilerLibcTypeLayouts
open Lean Miri.ABI

def layout (runtime : RuntimeMetadata) (name : String) : Except String (TyAndLayout TypeId) := do
  let some catalog := runtime.source.queries.libcTypeLayouts | throw "compiler libc type catalog absent"
  unless catalog.cratePath == #["libc"] do
    throw "compiler libc type query has wrong canonical crate path"
  unless catalog.namespaceName == "TypeNS" do
    throw "compiler libc type query has wrong namespace"
  let some (_, id) := catalog.entries.find? (·.1 == name) | throw s!"compiler libc type absent: {name}"
  runtime.lookup id |>.mapError toString
end Miri.Input.CompilerLibcTypeLayouts
