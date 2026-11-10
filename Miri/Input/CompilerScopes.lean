import Miri.Input.CompilerInstance
import Miri.Interpreter.VirtualCalls

/-! Exact SourceScopeData evidence for Body::caller_location_span (mir/mod.rs).
Body indices are explicit source identities; structural Body equality is never
used to discover an identity. Legacy absent inline metadata fails closed. -/
namespace Miri.Input.CompilerScopes
open Lean Miri.Interpreter
structure Entry where
  scope : VirtualCalls.CallerScope
  trackCaller : Option Bool
structure Prepared where
  program : LoweredProgram
  scopes : Array (Array (Except String Entry))
private def decodeEntry (ctx : LowerContext) (tables : CompilerTables) (scope : SourceScope) :
    Except String (Entry × CompilerTables) := do
  match scope.inlined with
  | none => pure (⟨⟨none,scope.inlinedParent⟩,none⟩,tables)
  | some inlined =>
    let _ ← CompilerInstance.source ctx inlined.instanceId
    unless inlined.callsiteSpanId < tables.spans.size do throw "inline callsite span ID out of bounds"
    let span : MIR.SpanRef := ⟨inlined.callsiteSpanId⟩
    pure (⟨⟨some (inlined.instanceId,span),scope.inlinedParent⟩,some inlined.requiresCallerLocation⟩,tables)

def prepare (program : LoweredProgram) : Prepared := Id.run do
  let ctx := LowerContext.ofDocument program.input
  let mut tables := program.compilerTables
  let mut all := #[]
  let executable := program.executableBodyIds
  for (body, bodyId) in program.bundle.bodies.toList.zipIdx do
    if !executable.contains bodyId then
      all := all.push #[]
      continue
    let mut entries := #[]
    let scopes := body.input.sourceScopes
    for index in [:scopes.size] do
      let result := do
        let some scope := scopes[index]? | throw "source scope canonical index missing"
        unless scope.id == index do throw "source scope index does not match canonical position"
        decodeEntry ctx tables scope
      match result with
      | .error e => entries := entries.push (.error e)
      | .ok (entry,next) =>
        tables := next
        entries := entries.push (.ok entry)
    all := all.push entries
  return ⟨program.withCompilerTables tables,all⟩

/-- The caller supplies the canonical body index from its frame identity map.
No fallback chooses a root, promoted body, or template by structural equality. -/
def sourceScope (prepared : Prepared) (bodyIndex scopeIndex : Nat) :
    Except String VirtualCalls.CallerScope := do
  let some scopes := prepared.scopes[bodyIndex]? | throw "unknown canonical body index"
  let some entry := scopes[scopeIndex]? | throw "unknown canonical source scope"
  pure (← entry).scope

/-- Full inlinecallee instances are the keys, including every generic argument. -/
def inlineRequiresCallerLocation (prepared : Prepared) (fnInstance : CallInstance) :
    Except String Bool := do
  let mut found := none
  for scopes in prepared.scopes do
    for entry in scopes do
      if let .ok entry := entry then
        if let some (callee,_) := entry.scope.inlined then
          if callee == fnInstance then
            let some track := entry.trackCaller | throw "missing inlinecallee track_caller query"
            if let some prior := found then
              unless prior == track do throw "conflicting inlinecallee track_caller query"
            found := some track
  let some result := found | throw "missing full-fnInstance requires_caller_location query"
  pure result
end Miri.Input.CompilerScopes
