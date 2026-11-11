import Miri.Input.CompilerFrameContext

/-! Allocation diagnostics follow pinned rustc interpret/stack.rs:345–377:
reverse the physical stack, expand each immediate inlined scope through its
parent_scope, and replace a physical dummy span by that instance's def_span.
Caller-location attributes and inlined_parent_scope are deliberately irrelevant. -/
namespace Miri.Input.CompilerAllocationBacktrace
open Miri.Interpreter

private def checkedSpan (spans : Array SourceSpanData) (span : MIR.SpanRef) :
    Except String SourceSpanData := do
  let some source := spans[span.id]? | throw "allocation backtrace span is absent"
  pure source

/-- The per-frame source algorithm, factored over the exact compiler tables so
physical, inlined and dummy-span cases can be checked independently of execution. -/
def frameTrace (spans : Array SourceSpanData) (instanceCount : Nat)
    (scopes : Array SourceScope) (physicalInstance : CallInstance)
    (definitionSpan : MIR.SpanRef) (source : Sum (MIR.SpanRef × Nat) MIR.SpanRef) :
    Except String (Array (CallInstance × MIR.SpanRef)) := do
  unless physicalInstance < instanceCount do throw "physical backtrace instance is absent"
  let (entries, span) ← match source with
    | .inr span => pure (#[], span)
    | .inl (span, scopeIndex) => do
      let rec expand (fuel scopeIndex : Nat) (span : MIR.SpanRef)
          (entries : Array (CallInstance × MIR.SpanRef)) :
          Except String (Array (CallInstance × MIR.SpanRef) × MIR.SpanRef) := do
        match fuel with
        | 0 => throw "cyclic allocation backtrace source scopes"
        | fuel + 1 =>
          let some scope := scopes[scopeIndex]? | throw "allocation backtrace source scope is absent"
          unless scope.id == scopeIndex do throw "allocation backtrace scope identity differs from its index"
          match scope.inlined with
          | none => pure (entries, span)
          | some inline =>
            unless inline.instanceId < instanceCount do throw "inlined backtrace instance is absent"
            let _ ← checkedSpan spans span
            let callSpan : MIR.SpanRef := ⟨inline.callsiteSpanId⟩
            let _ ← checkedSpan spans callSpan
            let some parent := scope.parent | throw "inlined backtrace scope has no parent"
            expand fuel parent callSpan (entries.push (inline.instanceId, span))
      expand (scopes.size + 1) scopeIndex span #[]
  let source ← checkedSpan spans span
  let span ← if source.isDummy then do
    let _ ← checkedSpan spans definitionSpan
    pure definitionSpan
  else pure span
  pure (entries.push (physicalInstance, span))

private def sourceOfFrame (frame : CompilerFrameContext.ActualFrame) :
    Except String (Sum (MIR.SpanRef × Nat) MIR.SpanRef) := do
  match frame.location with
  | .unwinding span => pure (.inr span)
  | .mir location =>
    let some block := frame.body.basicBlocks[location.block]? | throw "backtrace block is absent"
    let info ← if let some statement := block.statements[location.statementIndex]? then
        pure statement.sourceInfo
      else if location.statementIndex == block.statements.size then pure block.terminator.sourceInfo
      else throw "backtrace instruction is absent"
    pure (.inl (info.span, info.scope))

/-- Preserve each concrete full-instance identity and the actual active stack.
Invalid compiler metadata is an error; neither a nearby span nor a different
body with equal contents supplies missing evidence. -/
def collect (p : CompilerProviders.Prepared)
    (frames : Array CompilerFrameContext.ActualFrame) :
    Except String (Array (CallInstance × MIR.SpanRef)) := do
  let mut result := #[]
  for frame in frames.toList.reverse do
    let body ← CompilerFrameContext.bodyOfFrame p frame
    unless body.input.instanceId == frame.functionInstance do
      throw "allocation backtrace physical instance/body mismatch"
    let sourceInstance ← CompilerInstance.source p.program.input.instances frame.functionInstance
    let some definition := body.input.definitionId | throw "allocation backtrace body definition is absent"
    unless sourceInstance.instanceKind.defId == definition do
      throw "allocation backtrace def_span belongs to a different instance definition"
    let trace ← frameTrace p.program.input.spans p.program.input.instances.size
      body.input.sourceScopes frame.functionInstance ⟨body.input.preambleDefSpanId⟩
      (← sourceOfFrame frame)
    result := result ++ trace
  pure result
end Miri.Input.CompilerAllocationBacktrace
