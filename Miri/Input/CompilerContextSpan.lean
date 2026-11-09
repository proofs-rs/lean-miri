import Miri.Input.LowerMIR
import Miri.Input.Decoder

/-! eval.rs creates InterpCx with root_span=DUMMY_SP. The compiler exports that
actual span; it is interned into the same append-only table as MIR spans. -/
namespace Miri.Input.CompilerContextSpan
open Lean
private def source (program : LoweredProgram) : Except String TypedValue := do
  let session ← program.input.raw.getObjVal? "compiler_session_queries"
  let id ← (← session.getObjVal? "root_span").getNat?
  let some span := program.input.spans[id]? | throw "compiler root_span ID out of bounds"
  unless span.isDummy do throw "compiler root_span is not DUMMY_SP"
  pure (.sourceSpan id)

def prepare (program : LoweredProgram) : Except String LoweredProgram := do
  let (_,tables) ← lowerCompilerSpan program.compilerTables (← source program)
  pure (program.withCompilerTables tables)

def rootSpan (program : LoweredProgram) : Except String MIR.SpanRef := do
  let (span,tables) ← lowerCompilerSpan program.compilerTables (← source program)
  unless tables.spans == program.compilerTables.spans do
    throw "compiler root span is absent from final shared span table"
  pure span
end Miri.Input.CompilerContextSpan
