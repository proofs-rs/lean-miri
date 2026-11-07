import Miri.Input.CompilerInstance
import Miri.Interpreter.VirtualCalls

/-! Exact SourceScopeData evidence for Body::caller_location_span (mir/mod.rs).
Body indices are explicit source identities; structural Body equality is never
used to discover an identity. Missing inline metadata remains an error. -/
namespace Miri.Input.CompilerScopes
open Lean Miri.Interpreter
structure Entry where
  scope : VirtualCalls.CallerScope
  trackCaller : Option Bool
structure Prepared where
  program : LoweredProgram
  scopes : Array (Array (Except String Entry))
def prepare (program : LoweredProgram) : Prepared :=
  let scopes := program.input.mirTables.bodySources.map fun body => body.scopes.map fun source =>
    source.map fun entry => ⟨⟨entry.inlined,entry.parent⟩,entry.trackCaller⟩
  ⟨program,scopes⟩

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
