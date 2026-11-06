import Miri.Input.LowerMIR
import Miri.Input.Decoder

/-! eval.rs creates InterpCx with root_span=DUMMY_SP. The compiler exports that
actual span; it is interned into the same append-only table as MIR spans. -/
namespace Miri.Input.CompilerContextSpan
open Lean
private def source (program : LoweredProgram) : Except String TypedValue := do
  let session ← program.input.raw.getObjVal? "compiler_session_queries"
  let span ← session.getObjVal? "root_span"
  unless (← (← span.getObjVal? "is_dummy").getBool?) do throw "compiler root_span is not DUMMY_SP"
  decodeCompilerValueWithMemo span program.input.compilerValueMemo

def prepare (program : LoweredProgram) : Except String LoweredProgram := do
  let (_,tables) ← lowerCompilerSpan program.compilerTables (← source program)
  pure (program.withCompilerTables tables)

def rootSpan (program : LoweredProgram) : Except String MIR.SpanRef := do
  let (span,tables) ← lowerCompilerSpan program.compilerTables (← source program)
  unless tables.spans == program.compilerTables.spans do
    throw "compiler root span is absent from final shared span table"
  pure span

/-- Store the exact query outcome, including errors, for this final program.
Changing the program cannot retain a certificate from the previous tables. -/
structure Bound (program : LoweredProgram) where
  private mk ::
  result : Except String MIR.SpanRef
  private exact : result = rootSpan program

def bind (program : LoweredProgram) : Bound program :=
  ⟨rootSpan program, rfl⟩

theorem Bound.result_eq {program : LoweredProgram} (bound : Bound program) :
    bound.result = rootSpan program := bound.exact
end Miri.Input.CompilerContextSpan
