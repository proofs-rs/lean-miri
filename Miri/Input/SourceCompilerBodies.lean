import Miri.Input.SourceMirLowering
import Miri.Input.SourceCompilerWorld
import Miri.Input.LowerMIR
import Miri.Interpreter.BodyIdentity

/-! Body lookup over the current persistent source compiler World. No saved
instance/body array, body memo, query catalog or structural-body matching is
used. A source producer must derive/install a real body first; identity-only
handles do not acquire executable MIR from this adapter. -/
namespace Miri.Input.SourceCompilerBodies
open Miri.Interpreter

/-- Read and lower one actual body with the current canonical compiler tables.
The source producer and installation boundary remain responsible for deriving
its MIR and compiler facts. This lookup checks ownership rather than asserting
that arbitrary MIR is equivalent to a Rust source body. -/
def loweredBodyOfInstance (world : SourceCompilerWorld.World) (fnInstance : CallInstance) :
    Except String (BodyId × LoweredBody) := do
  let source ← SourceCompilerWorld.node world fnInstance
  let bodyId ← SourceCompilerWorld.bodyId world fnInstance
  let some body := world.canonical.bodies[bodyId]? | throw "source compiler actual body absent"
  let some definition := source.definitionId | throw "source compiler body owner definition absent"
  unless body.definitionId == some definition && source.instanceKind.defId == definition do
    throw "source compiler body/instance definition mismatch"
  let some _ := world.canonical.definitions[definition]? | throw "source compiler body DefId absent"
  -- Item keys retain the original DefId and complete arguments; numeric IDs
  -- are only handles within this same persistent World.
  if let .Item _ := source.instanceKind then
    let key ← SourceCompilerWorld.keyOf world fnInstance
    unless world.canonical.definitions[definition]? == some key.definition &&
        source.genericArgs == key.arguments do throw "source compiler body Item key mismatch"
  LocalValidation.validateBody body s!"source.bodies[{bodyId}]"
  let lowered ← lowerBody (LowerContext.ofDocument world.canonical) body.toBodyCore
  unless lowered.obligations.isEmpty do throw "source compiler loaded body has unresolved obligations"
  return (bodyId,lowered)

/-- The fixed interpreter receives its exact canonical body-table identity,
never an identity selected by equal MIR syntax, a path or a source span. -/
def loadedBodyOfInstance (world : SourceCompilerWorld.World) (fnInstance : CallInstance) :
    Except String LoadedBody := do
  let (bodyId,body) ← loweredBodyOfInstance world fnInstance
  return ⟨.ofCanonicalIndex bodyId,body.body⟩

/-- Derive the requested typed source body in the same persistent World before
loading. No captured document or pre-instantiated body table is consulted. -/
def demandLoadedBody (world : SourceCompilerWorld.World) (fnInstance : CallInstance) :
    Except String (SourceCompilerWorld.World × LoadedBody) := do
  let world ← SourceMirLowering.derive world fnInstance
  return (world,← loadedBodyOfInstance world fnInstance)

/-- Frame metadata must use this same current World. This rejects accidentally
combining a frame's old/wrong body identity with another instance's MIR. World
growth preserves existing indices; it does not authorize changing a frame key. -/
def frameBody (world : SourceCompilerWorld.World) (fnInstance : CallInstance)
    (identity : BodyIdentity) : Except String LoweredBody := do
  let (bodyId,body) ← loweredBodyOfInstance world fnInstance
  unless identity == .ofCanonicalIndex bodyId do throw "source compiler frame/body identity mismatch"
  return body

end Miri.Input.SourceCompilerBodies
