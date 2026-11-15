import Miri.Input.SourceCompilerWorld
import Miri.Input.RuntimeMetadata
import Miri.Interpreter.Step

/-! Live type/layout view over the evaluation-local compiler World. The target
was validated at initialization; reading a query does not validate the whole
source document again or merge another type interner into this identity space. -/
namespace Miri.Input.SourceCompilerRuntime
open Miri.Interpreter

def current (target : ABI.RuntimeTargetDataLayout) (access : SourceCompilerWorld.Access S) :
    EStateM StepError S RuntimeMetadata := do
  let some world := access.get (← get)
    | throw (.unsupported "source compiler runtime: World unavailable")
  return ⟨world.canonical,target⟩
end Miri.Input.SourceCompilerRuntime
