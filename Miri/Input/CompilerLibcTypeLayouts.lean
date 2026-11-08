import Miri.Input.RuntimeMetadata

/-! Exact `helpers.rs::libc_ty_layout` and `libc_array_ty_layout` path queries.
Names are looked up only in the exported `libc` TypeNS catalog; there is no
target-name fallback or layout-equality search. -/
namespace Miri.Input.CompilerLibcTypeLayouts
open Lean Miri.ABI

private def typeRef (entry : Json) : Except String TypeId := do
  let value := entry
  (← value.getObjVal? "type_id").getNat?

/-- Resolve one exact source libc type and require its imported compiler
layout. Missing or malformed metadata remains a demand-time error. -/
def layout (runtime : RuntimeMetadata) (name : String) : Except String (TyAndLayout TypeId) := do
  let catalog ← runtime.source.raw.getObjVal? "compiler_libc_type_layouts"
  unless (← (← catalog.getObjVal? "crate_path").getArr?) == #[toJson ("libc" : String)] do
    throw "compiler libc type query has wrong canonical crate path"
  unless (← (← catalog.getObjVal? "namespace").getStr?) == "TypeNS" do
    throw "compiler libc type query has wrong namespace"
  unless (← (← catalog.getObjVal? "typing_env").getStr?) == "fully_monomorphized" do
    throw "compiler libc type query has wrong typing environment"
  let entries ← catalog.getObjVal? "entries"
  let entry ← entries.getObjVal? name
  let id ← typeRef entry
  runtime.lookup id |>.mapError toString
end Miri.Input.CompilerLibcTypeLayouts
