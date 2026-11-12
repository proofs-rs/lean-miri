import Miri.Input.InstanceArena

/-! Diagnostic composite state used only by standalone interner component tests.
The interpreter uses RuntimeArrayTypes.World exclusively. No production module
imports this test support. -/
namespace Miri.Input.InstanceArena
open Miri.Interpreter GenericSubstitution

/-- Prototype of the one execution compiler world: type actions and instance
construction update this same value. Production integration is deliberately
withheld until raw body-role/ABI capabilities are complete. -/
structure World where
  types : TypeArena.World
  instances : Store
abbrev WorldM := StateT World (Except String)
private def lift [Monad m] [MonadExceptOf String m] (result : Except String α) : m α :=
  match result with | .ok value => pure value | .error error => throw error

def World.ofDocument (source : ImportDocument) : Except String World := do
  let types ← TypeArena.World.ofDocument source
  pure ⟨types,← Store.ofSource types source.instances⟩

def World.typeAction (action : TypeArena.WorldM α) : WorldM α := do
  let world ← get
  let (result,types) ← lift (action.run world.types)
  set {world with types}
  pure result

def World.internInstance (kind : CallInstanceKind) (arguments : Array MIR.GenericArg) : WorldM InstanceId := do
  let world ← get
  let key ← lift (Key.ofSource world.types kind arguments)
  let (id,instances) ← lift (world.instances.intern world.types key)
  set {world with instances}
  pure id

structure RawBodySource where
  definition : DefinitionIdentity
  source : CopyTemplateSource

/-- Role is explicit source material, not inferred from template order or paths.
This returns raw generic MIR only; it does not fabricate a body/instance ID. -/
def ordinaryBodySource (types : TypeArena.World) (sources : Array RawBodySource)
    (key : Key) : Except String CopyTemplateSource := do
  unless (← Key.ofSource types key.kind key.arguments) == key do
    throw "body request key physical definition does not match its kind"
  let .Item _ := key.kind | throw "ordinary Item body requested for another instance kind"
  let matching := sources.filter fun source => source.definition == key.definition && source.source.sourceRole == .runtime && source.source.sourcePromoted.isNone
  unless matching.size == 1 do throw "ordinary raw MIR source is absent or ambiguous"
  let some source := matching[0]? | throw "ordinary raw MIR source is absent"
  unless (← types.identity source.source.definitionId) == key.definition do
    throw "raw MIR source physical definition mismatch"
  pure source.source


end Miri.Input.InstanceArena
