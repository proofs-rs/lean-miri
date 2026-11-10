import Miri.Input.LowerMIR
import Miri.Input.Decoder

/-! eval.rs creates InterpCx with root_span=DUMMY_SP. The compiler exports that
actual span; it is interned into the same append-only table as MIR spans. -/
namespace Miri.Input.CompilerContextSpan
open Lean
def rootSpan (program : LoweredProgram) : Except String MIR.SpanRef := do
  let id := program.input.queries.session.rootSpan
  let some span := program.input.spans[id]? | throw "compiler root_span ID out of bounds"
  unless span.isDummy do throw "compiler root_span is not DUMMY_SP"
  pure ⟨id⟩

def prepare (program : LoweredProgram) : Except String LoweredProgram := do
  let _ ← rootSpan program
  pure program
end Miri.Input.CompilerContextSpan
