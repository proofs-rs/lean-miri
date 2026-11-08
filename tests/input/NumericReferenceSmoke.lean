import Miri.Input.Decoder

/-! Fresh exporter regression. Full and runtime decoding must agree about
execution readiness and retain document-local semantic ID spaces. -/
open Lean Miri.Input
set_option maxRecDepth 16384
set_option maxHeartbeats 0

def main (arguments : List String) : IO Unit := do
  let [path] := arguments | throw (IO.userError "expected one schema-4 MIR input")
  let text ← IO.FS.readFile path
  let full ← IO.ofExcept (decodeJson text)
  let runtime ← IO.ofExcept (decodeRuntimeJson text)
  unless full.document.types.map (·.id) == runtime.document.types.map (·.id) &&
      full.document.instances.map (·.id) == runtime.document.instances.map (·.id) &&
      full.document.allocations.map (·.id) == runtime.document.allocations.map (·.id) do
    throw (IO.userError "full/runtime identity tables disagree")
  for kind in SemanticTables.kinds do
    unless !(full.document.semanticTables.nodes kind).isEmpty do
      throw (IO.userError s!"fresh fixture did not exercise {kind.table}")
  IO.println s!"numeric wire: {full.document.types.size} types; all semantic kinds; ready"
