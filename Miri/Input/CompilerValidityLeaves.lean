import Miri.Input.CompilerProviders
import Miri.Input.CompilerCtfeValidity
import Miri.Input.CompilerPaths
import Miri.Input.RuntimeArrayFacts
import Miri.Interpreter.ExecutionValidity
import Miri.Interpreter.CompilerExecutionProviders

/-! Direct source validity compiler leaves. Physical Box projection uses the
canonical projection driver; CTFE allocation lookup executes the canonical
pointer/global algorithm and exact compiler static predicates.
No baseline visitor dictionary or successful missing-query defaults are needed. -/
namespace Miri.Input.CompilerValidityLeaves
open Miri.ABI Miri.Interpreter Miri.Memory
private def lift (value : Except String A) : EStateM StepError S A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (.unsupported s!"validity compiler query: {reason}")

def make (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (arrays : RuntimeArrayQueries.Access (ValidityMachine.State K U))
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) :
    ExecutionValidity.Leaves (ValidityMachine.State K U) C :=
  let facts := p.lifecycle.calls.symbols.facts
  let context := facts.context
  let run := fun {A} (action : TypeArena.WorldM A) => RuntimeArrayQueries.perform arrays action
  { classify := fun _ ty => run (CompilerFactAdapters.validityKindInWorld facts ty)
    unitLayout := fun _ => run (CompilerFacts.unitLayoutInWorld context)
    typeName := fun _ ty => run (CompilerFactAdapters.typeNameInWorld facts ty)
    opsemInhabited := fun _ ty => run (CompilerFacts.booleanInWorld context ty "opsem_inhabited")
    isFreeze := fun _ ty => run (CompilerFacts.booleanInWorld context ty "is_freeze")
    fieldPath := fun _ layout index child => run (CompilerPaths.fieldPathInWorld context layout index child)
    variantPath := fun _ layout index => run (CompilerPaths.variantPathInWorld context layout index)
    projectBox := CompilerExecutionProviders.projectBox context p.lifecycle.calls.runtime arrays projection
    metadataTail := fun _ ty => run (CompilerFactAdapters.metadataTailInWorld facts ty)
    ctfePointerLookup := CompilerCtfeValidity.lookup p image pointers }
end Miri.Input.CompilerValidityLeaves
