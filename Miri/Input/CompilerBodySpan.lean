import Miri.Input.CompilerProviders

/-! eval_context.rs::unwind_to_block records the exact current Body.span,
including before unwind termination. It does not use the preamble definition
span or an arbitrary statement span. Shared backtrace preparation interns this
compiler span; queries may not append isolated span identities at runtime. -/
namespace Miri.Input.CompilerBodySpan
open Miri.Interpreter

def get (p : CompilerProviders.Prepared)
    (types : RuntimeArrayQueries.Access (MachineHooks.State K U)) (frame : Frame P L E) :
    MachineHooks.M K U MIR.SpanRef := do
  unless frame.bodyIdentity.index < p.program.bodyCount do
    throw (.invalidProgram "unwind body identity absent from canonical compilation")
  let body ← p.resolveBody types frame.bodyIdentity.index
  unless body.body == frame.body do
    throw (.invalidProgram "unwind body identity/content mismatch")
  unless body.input.spanId < p.program.compilerTables.spans.size do
    throw (.unsupported "compiler body span absent from final shared span table")
  pure ⟨body.input.spanId⟩
end Miri.Input.CompilerBodySpan
