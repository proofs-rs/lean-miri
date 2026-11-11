import Miri.Input.CompilerAllocationBacktrace

open Miri Miri.Input Miri.Interpreter

private def sourceSpan (dummy : Bool := false) : SourceSpanData := {
  isDummy := dummy, lo := 0, hi := 1, start := ⟨1,0⟩, «end» := ⟨1,1⟩,
  context := "allocation-backtrace-test", file := 0 }
private def spans := #[sourceSpan true, sourceSpan, sourceSpan, sourceSpan, sourceSpan]
private def scopes : Array SourceScope := #[
  {id := 0, parent := none, spanId := 1, inlined := none, inlinedParent := none},
  {id := 1, parent := some 0, spanId := 2,
   inlined := some ⟨2,3,false⟩, inlinedParent := none},
  {id := 2, parent := some 1, spanId := 4,
   inlined := some ⟨3,2,true⟩, inlinedParent := some 0}]

private def expect (source : Sum (MIR.SpanRef × Nat) MIR.SpanRef)
    (expected : Array (CallInstance × MIR.SpanRef)) : IO Unit := do
  let actual := CompilerAllocationBacktrace.frameTrace spans 4 scopes 1 ⟨4⟩ source
  unless decide (actual.toOption = some expected) do
    throw (IO.userError s!"allocation trace mismatch: {reprStr actual}")

def main : IO Unit := do
  expect (.inl (⟨1⟩,0)) #[(1,⟨1⟩)]
  expect (.inr ⟨3⟩) #[(1,⟨3⟩)]
  expect (.inl (⟨0⟩,0)) #[(1,⟨4⟩)]
  expect (.inr ⟨0⟩) #[(1,⟨4⟩)]
  -- Physical parent_scope, not inlined_parent_scope; retain both generic
  -- instance IDs and both inline frames regardless of caller-location flags.
  expect (.inl (⟨1⟩,2)) #[(3,⟨1⟩),(2,⟨2⟩),(1,⟨3⟩)]
  -- Inline dummy spans are retained; only the physical frame gets def_span.
  expect (.inl (⟨0⟩,2)) #[(3,⟨0⟩),(2,⟨2⟩),(1,⟨3⟩)]
  let dummyCall := scopes.set! 1 {scopes[1] with inlined := some ⟨2,0,false⟩}
  unless decide ((CompilerAllocationBacktrace.frameTrace spans 4 dummyCall 1 ⟨4⟩
      (.inl (⟨1⟩,2))).toOption = some #[(3,⟨1⟩),(2,⟨2⟩),(1,⟨4⟩)]) do
    throw (IO.userError "physical dummy callsite did not use def_span")
  for malformed in [
      scopes.set! 1 {scopes[1] with inlined := some ⟨4,3,false⟩},
      scopes.set! 1 {scopes[1] with parent := none},
      scopes.set! 1 {scopes[1] with id := 99}] do
    if (CompilerAllocationBacktrace.frameTrace spans 4 malformed 1 ⟨4⟩ (.inl (⟨1⟩,2))).isOk then
      throw (IO.userError "invalid inline metadata accepted")
  for source in [Sum.inl (⟨99⟩,0), .inl (⟨1⟩,99)] do
    if (CompilerAllocationBacktrace.frameTrace spans 4 scopes 1 ⟨4⟩ source).isOk then
      throw (IO.userError "invalid source metadata accepted")
  let cycle := scopes.set! 2 {scopes[2] with parent := some 2}
  if (CompilerAllocationBacktrace.frameTrace spans 4 cycle 1 ⟨4⟩ (.inl (⟨1⟩,2))).isOk then
    throw (IO.userError "cyclic scope accepted")
  if (CompilerAllocationBacktrace.frameTrace spans 4 scopes 4 ⟨4⟩ (.inr ⟨1⟩)).isOk then
    throw (IO.userError "missing physical instance accepted")
  if (CompilerAllocationBacktrace.frameTrace spans 4 scopes 1 ⟨99⟩ (.inr ⟨0⟩)).isOk then
    throw (IO.userError "missing def_span accepted for dummy source")
  IO.println "allocation backtrace: physical, unwind, inline-parent, dummy spans and invalid metadata PASS"
