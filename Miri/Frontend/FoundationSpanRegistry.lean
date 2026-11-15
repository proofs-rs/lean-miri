import Miri.Frontend.FoundationSource
import Miri.Input.Model.Types

/-! Relocation of body-local exact rustc Span identities. Equal diagnostic
payloads with distinct compiler identities remain separate physical span rows. -/
namespace Miri.Frontend.Foundation
open Lean

structure SpanRegistry where
  files : Array String
  spans : Array Input.SourceSpanData
  compilerSpans : Array SourceSpan
  backtraces : Array Input.BacktraceSpan

private def internFile (files : Array String) (name : String) : Array String × Nat :=
  match files.findIdx? (· == name) with
  | some index => (files, index)
  | none => (files.push name, files.size)

/-- Construct physical source rows solely from captured compiler identities and
body-relative collapsed positions. No position is inferred from a span start. -/
def buildSpanRegistry (body : Json) : Except String SpanRegistry := do
  validateSourceMetadata body
  let backtraces ← sourceBacktraces body
  let mut sources := backtraces.map (·.span)
  let metadata ← body.getObjVal? "source_metadata"
  for scope in (← metadata.getObjValAs? (Array Json) "scopes") do
    sources := sources.push (← sourceSpan (← scope.getObjVal? "span"))
  for call in (← metadata.getObjValAs? (Array Json) "call_spans") do
    if call != Json.null then
      sources := sources.push (← sourceSpan (← call.getObjVal? "function"))
      let operand ← call.getObjVal? "function_operand"
      if operand != Json.null then
        sources := sources.push (← sourceSpan operand)
      for argument in (← call.getObjValAs? (Array Json) "arguments") do
        sources := sources.push (← sourceSpan argument)
  let sorted := sources.qsort (fun a b => a.identity < b.identity)
  let mut compilerSpans : Array SourceSpan := #[]
  for entry in sorted do
    if let some previous := compilerSpans[entry.identity]? then
      unless previous == entry do throw "conflicting compiler span identity"
    else
      unless entry.identity == compilerSpans.size do throw "non-dense compiler span identity"
      compilerSpans := compilerSpans.push entry
  let mut files := #[]
  let mut spans := #[]
  for entry in compilerSpans do
    let (updated, file) := internFile files entry.file
    files := updated
    spans := spans.push {
      isDummy := entry.isDummy, lo := entry.lo, hi := entry.hi
      start := ⟨entry.startLine, entry.startColumn⟩
      «end» := ⟨entry.endLine, entry.endColumn⟩
      context := entry.context, file : Input.SourceSpanData }
  let mut positions := #[]
  for entry in backtraces do
    let (updated, file) := internFile files entry.filename
    files := updated
    positions := positions.push {
      spanId := entry.span.identity
      position := ⟨entry.bytePosition, entry.line, entry.zeroBasedCharColumn, file⟩ : Input.BacktraceSpan }
  return ⟨files, spans, compilerSpans, positions⟩

/-- Parse the compiler's actual session DUMMY_SP. Its identity namespace is
session-local; callers relocate it after the body registry, without conflating
it with a body span that has the same local numeric identity. -/
def sessionRootSpan (document : Json) : Except String SourceSpan := do
  let session ← document.getObjVal? "session"
  let root ← sourceSpan (← session.getObjVal? "root_span")
  unless root.identity == 0 && root.isDummy && root.lo == 0 && root.hi == 0 &&
      root.parentLocalDefinition.isNone && root.context == "#0" do
    throw "invalid compiler session DUMMY_SP"
  return root

def appendSessionRootSpan (registry : SpanRegistry) (document : Json) :
    Except String (SpanRegistry × Nat) := do
  let root ← sessionRootSpan document
  let (files, file) := internFile registry.files root.file
  let row : Input.SourceSpanData := {
    isDummy := root.isDummy, lo := root.lo, hi := root.hi
    start := ⟨root.startLine, root.startColumn⟩
    «end» := ⟨root.endLine, root.endColumn⟩
    context := root.context, file }
  return ({ registry with files, spans := registry.spans.push row }, registry.spans.size)

end Miri.Frontend.Foundation
