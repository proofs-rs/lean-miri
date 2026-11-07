import Miri.Input.RuntimeMetadata

namespace Miri.Input.CompilerLibcTypeLayouts
open Miri.ABI

/-- Resolve the exact source libc TypeNS query and require its imported layout.
The reader validates the canonical crate path and typing environment; failures
remain demand-time errors with their producer reason. -/
def layout (runtime : RuntimeMetadata) (name : String) : Except String (TyAndLayout TypeId) := do
  let id ← CompilerTypeCatalogs.lookup runtime.source.compilerTypeCatalogs.libc name
  runtime.lookup id |>.mapError toString
end Miri.Input.CompilerLibcTypeLayouts
