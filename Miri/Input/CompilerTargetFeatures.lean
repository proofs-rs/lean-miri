import Miri.Input.CompilerIntrinsicFacts
import Miri.Interpreter.ExecutionCallLeaves

/-! machine.rs::check_fn_target_features exact compiler attributes/session.
Feature order and all Enabled/Forced/Implied kinds are retained in input. The
source driver performs the initial guard, diagnostic filtering and wasm abort.
-/
namespace Miri.Input.CompilerTargetFeatures
open Lean Miri.Interpreter
def required (p : CompilerIntrinsicFacts.Prepared) (callee : CallInstance) :
    Except String (Array ExecutionCallLeaves.TargetFeature) := do
  let some entry := p.entries.find? (·.callee == callee) | throw "missing exact full-instance target features"
  return (← entry.data.targetFeatures).map fun (name,implied) => ⟨name,implied⟩

def available (p : CompilerIntrinsicFacts.Prepared) (name : String) : Except String Bool := do
  let session ← p.program.input.mirTables.sessionMetadata
  pure ((← session.internalTargetFeatures).contains name)

def isLikeWasm (p : CompilerIntrinsicFacts.Prepared) : Except String Bool := do
  (← p.program.input.mirTables.sessionMetadata).isLikeWasm
private def lift (query : Except String A) : EStateM StepError S A :=
  match query with | .ok value => pure value | .error error => throw (.unsupported error)

def dictionary (p : CompilerIntrinsicFacts.Prepared) : ExecutionCallLeaves.TargetFeatures S :=
  {required := fun callee => lift (required p callee)
   available := fun name => lift (available p name)
   isLikeWasm := lift (isLikeWasm p)}
end Miri.Input.CompilerTargetFeatures
