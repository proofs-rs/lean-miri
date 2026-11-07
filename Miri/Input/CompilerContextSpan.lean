import Miri.Input.LowerMIR
import Miri.Input.Decoder

/-! eval.rs creates InterpCx with root_span=DUMMY_SP. The compiler exports that
actual span; it is interned into the same append-only table as MIR spans. -/
namespace Miri.Input.CompilerContextSpan
open Lean
private def source (program : LoweredProgram) : Except String TypedValue := do
  let some id := program.input.rootSpan | throw "compiler root span absent"
  let span ← program.input.sourceSpans.lookup id |>.mapError fun id => s!"invalid compiler root span {id}"
  return .sourceSpan span

def prepare (program : LoweredProgram) : Except String LoweredProgram := do
  let (_,tables) ← lowerCompilerSpan program.compilerTables (← source program)
  pure (program.withCompilerTables tables)

def rootSpan (program : LoweredProgram) : Except String MIR.SpanRef := do
  let (span,tables) ← lowerCompilerSpan program.compilerTables (← source program)
  unless tables.spans == program.compilerTables.spans do
    throw "compiler root span is absent from final shared span table"
  pure span
end Miri.Input.CompilerContextSpan
