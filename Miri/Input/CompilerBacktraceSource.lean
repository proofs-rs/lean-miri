import Miri.Input.WorldInstanceName
import Miri.Input.CompilerInstance
import Miri.Input.RuntimeArrayQueries
import Miri.Input.LowerMIR
import Miri.Interpreter.Backtrace
import Miri.Interpreter.BacktraceMachine

/-! Compiler hygiene/source-map/rendering evidence, with exact body/span keys.
An unseen forged BytePos remains unresolved; no nearby-position approximation. -/
namespace Miri.Input.CompilerBacktraceSource
open Lean Miri.Interpreter
structure Position where
  bytePosition : UInt32
  line : Nat
  column : Nat
  filename : Nat
  deriving DecidableEq
structure SpanEntry where
  span : MIR.SpanRef
  position : Position
structure Prepared where
  program : LoweredProgram
  positions : Array Position
  names : Array (CallInstance × String)

private def position (files : Array String) (source : CompilerSourcePosition) : Except String Position := do
  unless source.filename < files.size do throw "backtrace filename ID out of bounds"
  unless source.bytePosition < 2^32 do throw "compiler BytePos exceeds u32"
  pure ⟨UInt32.ofNat source.bytePosition,source.line,source.column,source.filename⟩
private def spans (files : Array String) (ctx : LowerContext) (tables : CompilerTables) (rows : Array BacktraceSpan) :
    Except String (Array SpanEntry × CompilerTables) := do
  let mut tables := tables
  let mut entries := #[]
  for record in rows do
    unless record.spanId < tables.spans.size do throw "backtrace span ID out of bounds"
    let span : MIR.SpanRef := ⟨record.spanId⟩
    let location ← position files record.position
    if let some old := entries.find? (fun entry : SpanEntry => entry.span == span) then
      unless old.position == location do throw "conflicting body/span hygiene query"
    else entries := entries.push ⟨span,location⟩
  return (entries,tables)

def prepare (program : LoweredProgram) : Except String Prepared := do
  let ctx := LowerContext.ofDocument program.input
  let mut tables := program.compilerTables
  let mut positions := #[]
  let mut positionIndex : Std.HashMap UInt32 Position := {}
  for index in [:program.bodyCount] do
    let source := do
      let metadata ← program.bodyMetadata index
      spans program.input.files ctx tables metadata.backtraceSpans
    match source with
    | .error _ => pure ()
    | .ok (entries,next) =>
      tables := next
      for entry in entries do
        if let some old := positionIndex.get? entry.position.bytePosition then
          unless old == entry.position do throw "conflicting exact source-map query"
        else
          positionIndex := positionIndex.insert entry.position.bytePosition entry.position
          positions := positions.push entry.position
  -- Undemanded raw templates also own immutable source-map positions.
  -- Retaining them does not instantiate a body or assign a runtime body ID.
  for source in program.input.mirTemplates do
    let entries ← match spans program.input.files ctx tables source.backtraceSpans with
      | .ok (entries,_) => pure entries
      | .error _ => pure #[]
    for entry in entries do
      if let some old := positionIndex.get? entry.position.bytePosition then
        unless old == entry.position do throw "conflicting exact source-map query"
      else
        positionIndex := positionIndex.insert entry.position.bytePosition entry.position
        positions := positions.push entry.position
  let ctx := LowerContext.ofDocument program.input
  let records := program.input.queries.runtime.instances
  let mut names := #[]
  let mut namesByDefinition : Std.HashMap Nat (Array Nat) := {}
  for record in records do
    let callee := record.instanceId
    let _ ← CompilerInstance.Material.source ctx.instances callee
    let name := record.display
    let candidates := namesByDefinition.getD callee #[]
    if let some index := candidates.find? fun index =>
        match names[index]? with
        | some (oldCallee,_) => oldCallee == callee
        | none => false then
      let some (_,old) := names[index]? | throw "compiler full-instance bucket index invariant"
      unless old == name do throw "conflicting compiler full-instance rendering"
    else
      let index := names.size
      names := names.push (callee,name)
      namesByDefinition := namesByDefinition.insert callee (candidates.push index)
  return ⟨program.withCompilerTables tables,positions,names⟩

private def lift (result : Except String A) : EStateM StepError S A :=
  match result with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler backtrace source: {error}")

def collapsedSpan (p : Prepared) (types : RuntimeArrayQueries.Access S)
    (identity : BodyIdentity) (span : MIR.SpanRef) : EStateM StepError S UInt32 := do
  let metadata ← RuntimeArrayQueries.performCompiler types (SourceMir.metadataIdentity identity)
  lift do
    let (entries,_) ← spans p.program.input.files (LowerContext.ofDocument p.program.input)
      p.program.compilerTables metadata.backtraceSpans
    let some entry := entries.find? (·.span == span) | throw "exact body/span hygiene query absent"
    pure entry.position.bytePosition

private def renderInstance (p : Prepared) (types : RuntimeArrayQueries.Access S)
    (callee : CallInstance) : EStateM StepError S String := do
  RuntimeArrayQueries.performCompiler types do
    let world ← get
    let key ← match ← world.instances.lookup callee with
      | .material key | .constructed key => pure key
    if WorldInstanceName.supports world key then
      WorldInstanceName.query 16384 key
    else
      let some (_,name) := p.names.find? (·.1 == callee)
        | throw "exact residual full-instance rendering absent"
      pure name

/-- Compiler-source construction with only runtime global/pointer queries.
Every hygiene/source-map/name result is selected by its exact exported key. -/
def source (p : Prepared) (types : RuntimeArrayQueries.Access S) (hostUsizeMax : Nat)
    (unitPointerLayout : EStateM StepError S LocalLayout)
    (misaligned : Memory.Pointer (Option Memory.Provenance) → ABI.Align → EStateM StepError S (Option Memory.Misalignment))
    (functionPointer : CallInstance → EStateM StepError S (Memory.Pointer (Option Memory.Provenance)))
    (allocation : Memory.Pointer (Option Memory.Provenance) → EStateM StepError S (Memory.AllocId × ABI.Size))
    (globalFunction : Memory.AllocId → EStateM StepError S (Option CallInstance)) :
    BacktraceMachine.Sources S Position := {
  hostUsizeMax,unitPointerLayout,misaligned,functionPointer,allocation,globalFunction
  collapsedSpanLo := collapsedSpan p types
  lookupCharPos := fun offset => lift do
    let some location := p.positions.find? (·.bytePosition == offset)
      | throw "unseen BytePos needs actual compiler source-map query"
    return location
  line := Position.line
  column := Position.column
  renderInstance := renderInstance p types
  remappedFilename := fun location => lift do
    let some filename := p.program.input.files[location.filename]?
      | throw "backtrace filename ID out of bounds"
    return filename }

def hooks (p : Prepared) (types : RuntimeArrayQueries.Access S) (base : Backtrace.Hooks P S D MD B I E Position) :
    Backtrace.Hooks P S D MD B I E Position :=
  {base with
    collapsedSpanLo := collapsedSpan p types
    lookupCharPos := fun offset => lift do
      let some location := p.positions.find? (·.bytePosition == offset)
        | throw "unseen BytePos needs actual compiler source-map query"
      return location
    line := Position.line
    column := Position.column
    renderInstance := renderInstance p types
    remappedFilename := fun location => lift do
      let some filename := p.program.input.files[location.filename]?
        | throw "backtrace filename ID out of bounds"
      return filename }
end Miri.Input.CompilerBacktraceSource
