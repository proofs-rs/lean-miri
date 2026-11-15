import Lean

/-! Source metadata retained by finite-material export. These are source facts;
no executable body or query answer is constructed here. Span contexts and file
names are rustc diagnostic renderings, as in the existing MIR exporter. -/
namespace Miri.Frontend.Foundation
open Lean

set_option autoImplicit false in
structure SourceSpan where
  identity : Nat
  parentLocalDefinition : Option Nat
  isDummy : Bool
  lo : Nat
  hi : Nat
  context : String
  file : String
  startLine : Nat
  startColumn : Nat
  endLine : Nat
  endColumn : Nat
  deriving Repr, DecidableEq

set_option autoImplicit false in
structure SourceInfo where
  span : SourceSpan
  scope : Nat
  deriving Repr, DecidableEq

def sourceSpan (j : Json) : Except String SourceSpan := do
  let start ← j.getObjVal? "start"
  let finish ← j.getObjVal? "end"
  let result : SourceSpan := {
    identity := ← j.getObjValAs? Nat "span_id"
    parentLocalDefinition := ← j.getObjValAs? (Option Nat) "parent_local_definition"
    isDummy := ← j.getObjValAs? Bool "is_dummy"
    lo := ← j.getObjValAs? Nat "lo"
    hi := ← j.getObjValAs? Nat "hi"
    context := ← j.getObjValAs? String "ctxt"
    file := ← j.getObjValAs? String "file"
    startLine := ← start.getObjValAs? Nat "line"
    startColumn := ← start.getObjValAs? Nat "column"
    endLine := ← finish.getObjValAs? Nat "line"
    endColumn := ← finish.getObjValAs? Nat "column"
  }
  unless result.lo ≤ result.hi do throw "source span has reversed byte positions"
  return result

structure SourceBacktrace where
  span : SourceSpan
  bytePosition : Nat
  line : Nat
  zeroBasedCharColumn : Nat
  filename : String
  deriving Repr, DecidableEq

/-- Compiler body-relative hygiene-collapsed positions, distinct from raw
source-span starts. Filenames use rustc's remapped display path. -/
def sourceBacktraces (body : Json) : Except String (Array SourceBacktrace) := do
  let metadata ← body.getObjVal? "source_metadata"
  let records ← metadata.getObjValAs? (Array Json) "backtrace_spans"
  let mut result := #[]
  for record in records do
    let position ← record.getObjVal? "source_position"
    let entry : SourceBacktrace := {
      span := ← sourceSpan (← record.getObjVal? "span")
      bytePosition := ← position.getObjValAs? Nat "byte_position"
      line := ← position.getObjValAs? Nat "line"
      zeroBasedCharColumn := ← position.getObjValAs? Nat "zero_based_char_column"
      filename := ← position.getObjValAs? String "filename"
    }
    unless entry.bytePosition < 2^32 do throw "backtrace byte position exceeds rustc BytePos"
    if result.any (fun previous => previous.span == entry.span) then
      throw "duplicate source backtrace span"
    result := result.push entry
  return result

private def info (scopeCount : Nat) (j : Json) : Except String SourceInfo := do
  let scope ← j.getObjValAs? Nat "scope"
  unless scope < scopeCount do throw "source scope is out of bounds"
  return ⟨← sourceSpan (← j.getObjVal? "span"), scope⟩

/-- Check identities and parallel source arrays against the captured MIR spine.
Inlining is rejected by the producer and remains unsupported here. -/
def validateSourceMetadata (body : Json) : Except String Unit := do
  let source ← body.getObjVal? "source_metadata"
  let mut required := #[← sourceSpan (← source.getObjVal? "span"),
    ← sourceSpan (← source.getObjVal? "definition_span")]
  let backtraces ← sourceBacktraces body
  let phase ← source.getObjVal? "phase"
  unless (← phase.getObjValAs? String "kind") == "runtime" do
    throw "source body is not runtime MIR"
  let _ ← source.getObjVal? "injection_phase"
  let scopes ← source.getObjValAs? (Array Json) "scopes"
  for h : i in [:scopes.size] do
    let scope := scopes[i]
    let _ ← sourceSpan (← scope.getObjVal? "span")
    let parent ← scope.getObjValAs? (Option Nat) "parent"
    if let some parent := parent then
      unless parent < i do throw "source scope parent must precede child"
    unless (← scope.getObjValAs? (Option Nat) "inlined_parent").isNone do
      throw "inlined source metadata is unsupported"
  let locals ← body.getObjValAs? (Array Json) "locals"
  let declarations ← source.getObjValAs? (Array Json) "locals"
  unless declarations.size == locals.size do throw "source local count mismatch"
  for declaration in declarations do
    let _ ← declaration.getObjValAs? Bool "mutable"
    let entry ← info scopes.size (← declaration.getObjVal? "source_info")
    required := required.push entry.span
  let blocks ← body.getObjValAs? (Array Json) "blocks"
  let locations ← source.getObjValAs? (Array Json) "blocks"
  unless blocks.size == locations.size do throw "source block count mismatch"
  let callSpans ← source.getObjValAs? (Array Json) "call_spans"
  unless callSpans.size == blocks.size do throw "source call span count mismatch"
  for (block, location) in blocks.zip locations do
    let statements ← block.getObjValAs? (Array Json) "statements"
    let sources ← location.getObjValAs? (Array Json) "statements"
    unless statements.size == sources.size do throw "source statement count mismatch"
    for entry in sources do
      required := required.push (← info scopes.size entry).span
    required := required.push (← info scopes.size (← location.getObjVal? "terminator")).span
  for (block, call) in blocks.zip callSpans do
    if (← (← block.getObjVal? "terminator").getObjValAs? String "kind") == "call" then
      let _ ← sourceSpan (← call.getObjVal? "function")
      let functionOperand ← call.getObjVal? "function_operand"
      if functionOperand != Json.null then
        let _ ← sourceSpan functionOperand
      let arguments ← (← block.getObjVal? "terminator").getObjValAs? (Array Json) "arguments"
      let spans ← call.getObjValAs? (Array Json) "arguments"
      unless spans.size == arguments.size do throw "call argument source span count mismatch"
      for span in spans do
        let _ ← sourceSpan span
    else unless call == Json.null do throw "non-call has call source spans"
  for entry in required do
    unless backtraces.any (fun b => b.span == entry) do
      throw "missing compiler backtrace source span"
  for entry in backtraces do
    unless required.contains entry.span do throw "unexpected compiler backtrace source span"

/-- Derive storage initialization from finite MIR markers. Pinned rustc
`always_storage_live_locals` removes locals mentioned by either StorageLive or
StorageDead; the return place and arguments are initialized separately. -/
def alwaysStorageLive (body : Json) : Except String (Array Bool) := do
  let declarations ← body.getObjValAs? (Array Json) "locals"
  let mut result := Array.replicate declarations.size true
  for block in (← body.getObjValAs? (Array Json) "blocks") do
    for statement in (← block.getObjValAs? (Array Json) "statements") do
      let kind ← statement.getObjValAs? String "kind"
      if kind == "storage_live" || kind == "storage_dead" then
        let index ← statement.getObjValAs? Nat "local"
        if h : index < result.size then
          result := result.set index false
        else throw "storage marker local is out of bounds"
  return result

end Miri.Frontend.Foundation
