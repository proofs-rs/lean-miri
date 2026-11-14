import Miri.Input.RuntimeArrayTypes
import Miri.Input.WorldTrivialAutoTraits
import Miri.Input.WorldDynamicAutoTrait

namespace Miri.Input.WorldSourceAutoTraits
open GenericSubstitution
private def liftPure (result : Except String α) : RuntimeArrayTypes.CompilerM α :=
  match result with | .ok value => pure value | .error error => throw error

def query (id : TypeId) (languageItem : String) : RuntimeArrayTypes.CompilerM Bool := do
  let world ← get
  if ← liftPure (WorldTrivialAutoTraits.query world.arena 16384 id) then return true
  let context := world.metadata.normalizationContext
  let declarations := context.traits.traits.filter (·.langItem == some languageItem)
  let #[declaration] := declarations | throw s!"ABI source trait absent or ambiguous: {languageItem}"
  if let some answer ← WorldDynamicAutoTrait.query 16384 id declaration then return answer
  let ty ← liftPure (GenericInstantiationWorld.ofType world.arena 16384 id)
  match ← liftPure (AliasRuntime.solveGoal context 16384 100000
      ⟨.positive,⟨declaration.definition,#[ty]⟩⟩) with
  | .proven _ => pure true
  | .noSolution => pure false
  | .ambiguous reason => throw s!"ABI source trait is ambiguous: {reason}"

end Miri.Input.WorldSourceAutoTraits
