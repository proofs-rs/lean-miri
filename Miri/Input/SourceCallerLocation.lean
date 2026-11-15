import Miri.Input.SourceCompilerFrame
import Miri.Interpreter.VirtualCalls

/-! Pinned instance.rs::requires_caller_location and canonical SourceScopeData.
Definition attributes are finite source facts, not per-instance query answers.
No span is synthesized, and no saved scope/instance table supplies a source
mode result. -/
namespace Miri.Input.SourceCallerLocation
open Miri.Interpreter

def requiresCallerLocation (world : SourceCompilerWorld.World) (callee : CallInstance) : Except String Bool := do
  let node ← SourceCompilerWorld.node world callee
  match node.instanceKind with
  | .Item definition | .Virtual definition _ | .Shim (.VTable definition) =>
    let some raw := world.canonical.definitions[definition]? | throw "caller-location definition absent"
    let some source := world.canonical.sourceMaterial | throw "caller-location source unavailable"
    let some types := source.physical | throw "caller-location definition source unavailable"
    let [declaration] := (types.definitions.filter (·.raw == raw)).toList
      | throw "caller-location source definition absent/ambiguous"
    unless #["fn","assoc_fn","closure"].contains declaration.kind do
      throw "caller-location definition kind unsupported"
    let some abi := source.abi | throw "caller-location definition attributes unavailable"
    let [header] := (abi.functions.filter (·.definition == raw)).toList
      | throw "caller-location definition attributes absent/ambiguous"
    return header.attributes.trackCaller
  | .Shim (.ClosureOnce _ _ trackCaller) => return trackCaller
  | .Intrinsic _ | .LlvmIntrinsic _ | .Shim _ => return false

private def spanPresent (world : SourceCompilerWorld.World) (id : Nat) : Except String Unit := do
  let some span := world.canonical.spans[id]? | throw "caller-location span absent"
  unless span.lo ≤ span.hi && span.file < world.canonical.files.size do
    throw "caller-location span payload invalid"

/-- Read the checked body associated with the exact frame instance/body key.
Inline TRACK_CALLER is derived separately from the current callee definition;
the old inlined requiresCallerLocation answer field is deliberately unused. -/
def sourceScope (world : SourceCompilerWorld.World) (identity : BodyIdentity) (callee : CallInstance)
    (mir : MIR.Body) (index : Nat) : Except String VirtualCalls.CallerScope := do
  let body ← SourceCompilerFrame.body world callee identity mir
  let some scope := body.sourceScopes[index]? | throw "caller-location source scope absent"
  unless scope.id == index do throw "caller-location scope index mismatch"
  spanPresent world scope.spanId
  if let some parent := scope.inlinedParent then
    unless parent < body.sourceScopes.size do throw "caller-location inline-parent scope absent"
  let inlined ← match scope.inlined with
    | none => pure none
    | some inlined => do
      let _ ← SourceCompilerWorld.node world inlined.instanceId
      spanPresent world inlined.callsiteSpanId
      pure (some (inlined.instanceId,MIR.SpanRef.mk inlined.callsiteSpanId))
  return ⟨inlined,scope.inlinedParent⟩
end Miri.Input.SourceCallerLocation
