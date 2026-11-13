import Miri.Input.RuntimeMetadata
import Miri.Input.AliasNormalization
import Miri.Input.RuntimeArrayQueries

namespace Miri.Input.RuntimeEffectfulLayout
open Miri.Interpreter GenericSubstitution
set_option autoImplicit false
variable {S A : Type}

/-- Must perform genuine type-level VALTREE demand and retain the entire owning
runtime successor. There is no evaluated scalar or normalized-table capability. -/
abbrev Provider (S : Type) := CompilerTypingEnv.Env → TypeId → Option MIR.SpanRef → Term → RvalueM S Term

/-- Missing engine capability remains a failure at the actual constant demand. -/
def unavailable : Provider S := fun _ _ _ _ =>
  throw (.unsupported "runtime type-level constant requires an effectful VALTREE/ALLOC provider with its physical VALUE dependencies")

/-- Source String errors are a separate layer. Runtime provider StepError
failures bypass this layer, retaining the runtime EStateM successor unchanged. -/
abbrev SourceM (S : Type) := ExceptT String (RvalueM S)

private def getRuntime : SourceM S S := liftM (getThe S : RvalueM S S)
private def setRuntime (state : S) : SourceM S Unit := liftM (set state : RvalueM S Unit)

def perform (types : RuntimeArrayQueries.Access S) (provider : Provider S)
    (environment : CompilerTypingEnv.Env) (usage : Option MIR.SpanRef)
    (metadata : RuntimeMetadata)
    (query : ∀ {m : Type → Type} [Monad m] [MonadStateOf TypeArena.World m]
      [MonadExceptOf String m] [MonadLiftT (Except String) m] [MonadLiftT TypeArena.WorldM m],
      RuntimeMetadata.LayoutNormalization m → m A)
    (sourceError : String → StepError := fun message => .unsupported s!"runtime source layout: {message}") : RvalueM S A := do
  let action : SourceM S A := do
    letI : MonadStateOf TypeArena.World (SourceM S) := {
      get := do pure (types.get (← getRuntime)).arena
      set := fun arena => do
        let current ← getRuntime
        setRuntime (types.set current {(types.get current) with arena})
      modifyGet := fun update => do
        let current ← getRuntime
        let (result,arena) := update (types.get current).arena
        setRuntime (types.set current {(types.get current) with arena})
        pure result }
    letI : MonadLift (Except String) (SourceM S) := {
      monadLift := fun result => ExceptT.mk (pure result) }
    letI : MonadLift TypeArena.WorldM (SourceM S) := {
      monadLift := fun sourceAction => do
        let current ← getRuntime
        match sourceAction.run (types.get current).arena with
        | .error message => throw message
        | .ok (value,arena) =>
          setRuntime (types.set current {(types.get current) with arena})
          pure value }
    let context := metadata.normalizationContext
    let normalize : Nat → Nat → Term → SourceM S TypeId := fun work fuel term => do
      let isScoped ← TraitSelection.Match.requiresQuantified fuel term
      let term ← if isScoped then ScopedNormalization.prepareAliases 0 fuel term
        else MirTemplate.eraseFreeRegions fuel term
      unless isScoped do MirTemplate.validateClosed fuel term
      let pureHooks := AliasRuntime.normalizationHooks context 0 work fuel #[]
      let hooks : AliasNormalization.EffectHooks (SourceM S) := {
        toHooks := pureHooks
        constant := fun remaining source => do
          let .definition .constant "alias_anonymous_not_rigid" definition .nil := source
            | throw "effectful type constant requires separate generic/trait/rigid source admission"
          let arena := (types.get (← getRuntime)).arena
          let reference ← arena.definitionRef definition
          let some declaration := arena.definitions[reference]?
            | throw "type constant source declaration absent"
          let some template := declaration.genericTemplate
            | throw "type constant raw declared type template absent"
          let expectedTerm ← template.instantiateType remaining #[]
          let expected ← GenericInstantiationWorld.resolveType remaining expectedTerm
          -- Lift the runtime provider, not its error into a source String.
          -- A provider failure never enters ExceptT's String catch channel.
          liftM (provider environment expected usage source) }
      let result ← if isScoped then
        AliasNormalization.normalizeInUniverseEffectful 0 context.aliases hooks fuel #[] term
        else AliasNormalization.normalizeEffectful context.aliases hooks fuel #[] term
      let result ← if isScoped || (← TraitSelection.Match.requiresQuantified fuel result) then
        ScopedNormalization.normalize 0 fuel result
        else do
          let result ← MirTemplate.eraseFreeRegions fuel result
          MirTemplate.validateClosed fuel result
          pure result
      GenericInstantiationWorld.resolveType fuel result
    query (m := SourceM S) {toContext := context,resolve := normalize}
  match ← action.run with
  | .ok value => pure value
  | .error message => throw (sourceError message)
def layout (types : RuntimeArrayQueries.Access S) (provider : Provider S)
    (environment : CompilerTypingEnv.Env) (usage : Option MIR.SpanRef)
    (metadata : RuntimeMetadata) (id : TypeId) : RvalueM S (Miri.ABI.TyAndLayout TypeId) :=
  perform types provider environment usage metadata fun {_} _ _ _ _ _ normalization =>
    RuntimeMetadata.layoutEffectfulInWorld normalization metadata id

def fieldType (types : RuntimeArrayQueries.Access S) (provider : Provider S)
    (environment : CompilerTypingEnv.Env) (usage : Option MIR.SpanRef)
    (metadata : RuntimeMetadata) (id variant index : Nat) : RvalueM S TypeId :=
  perform types provider environment usage metadata fun {_} _ _ _ _ _ normalization =>
    RuntimeMetadata.fieldTypeEffectfulInWorld normalization metadata id variant index

def fieldLayout (types : RuntimeArrayQueries.Access S) (provider : Provider S)
    (environment : CompilerTypingEnv.Env) (usage : Option MIR.SpanRef)
    (metadata : RuntimeMetadata) (parent : Miri.ABI.TyAndLayout TypeId) (index : Nat) :
    RvalueM S (Miri.ABI.TyAndLayout TypeId) :=
  perform types provider environment usage metadata fun {_} _ _ _ _ _ normalization =>
    RuntimeMetadata.fieldLayoutForEffectfulInWorld normalization metadata parent index
def normalizeType (types : RuntimeArrayQueries.Access S) (provider : Provider S)
    (environment : CompilerTypingEnv.Env) (usage : Option MIR.SpanRef)
    (metadata : RuntimeMetadata) (id : TypeId) : RvalueM S TypeId :=
  perform types provider environment usage metadata fun {_} _ _ _ _ _ normalization => do
    let arena ← get
    let fuel := metadata.materialLayoutFuel + 3 * (arena.constructedTypes.size + arena.constructedConstants.size)
    let term ← GenericInstantiationWorld.ofType arena fuel id
    normalization.resolve (fuel * (fuel + 1)) fuel term

def pointerMetadataType (types : RuntimeArrayQueries.Access S) (provider : Provider S)
    (environment : CompilerTypingEnv.Env) (usage : Option MIR.SpanRef)
    (metadata : RuntimeMetadata) (id : TypeId) : RvalueM S TypeId :=
  perform types provider environment usage metadata fun {_} _ _ _ _ _ normalization =>
    RuntimeMetadata.pointerMetadataTypeEffectfulInWorld normalization metadata id
end Miri.Input.RuntimeEffectfulLayout
