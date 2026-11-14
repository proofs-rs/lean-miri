import Miri.Input.RuntimeArrayTypes
import Miri.Input.CoroutineSourceInstantiation

/-! Connect source physical owner to the existing BodyArena interner.
No raw auxiliary drop snapshot becomes callable. Requires fresh runtime templates
for the exact selected physical owner; absent MIR remains unsupported. -/
namespace Miri.Input.CoroutineBodyWorld
open RuntimeArrayTypes

def intern (fuel : Nat) (coroutineType : TypeId) : CompilerM BodyId := do
  let world ← get
  let some coverage := world.metadata.source.coroutineCoverage |
    throw "coroutine body source catalog absent"
  let term ← liftType do GenericInstantiationWorld.ofType (← get) fuel coroutineType
  let selected ← match CoroutineSourceInstantiation.instantiate coverage.genericSources fuel term with
    | .ok value => pure value | .error error => throw error
  let arena ← liftType get
  let physical ← match arena.definitionRef selected.source.physicalOwner with
    | .ok value => pure value | .error error => throw error
  let key ← match arena.lookupType coroutineType with
    | .error error => throw error
    | .ok (.constructed key) => pure key
    | .ok (.material node) => match arena.materialKey node with
      | .ok (some key) => pure key
      | .ok none => throw "coroutine body material constructor absent"
      | .error error => throw error
  let .coroutine _ arguments := key | throw "coroutine body constructor absent"
  let templates := world.metadata.source.mirTemplates.zipIdx.filter fun (source,_) =>
    source.definitionId == physical && source.sourceRole == .runtime && source.sourcePromoted.isNone
  let #[(source,templateId)] := templates |
    throw "coroutine body raw runtime template missing or ambiguous"
  unless source.template.parameters == selected.source.parameters do
    throw "coroutine body source template parameter domain differs"
  let sourceInstance ← internInstance (.Item physical) arguments
  internBody templateId sourceInstance none .runtime

end Miri.Input.CoroutineBodyWorld
