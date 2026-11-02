import empty_function.BodyDictionaries
import empty_function.BodyValidation

/-! Unit validation derived from the actual canonical factory and pure compiler
metadata, at an arbitrary caller/memory/thread state with a fresh unit local. -/
namespace EmptyFunction.BodyCanonicalValidation
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

 theorem unit (p : CompilerProviders.Prepared) (image : AllocationImage.Imported)
    (bytes : CompilerGlobalBytes.Prepared) (options : EvalConfigurationCore.Options)
    (leaves : RootLeaves) (remaining : Nat) (contract : Construction p) (config : Config)
    (built : EvalConfigurationCore.make p image bytes options leaves () (remaining+1) = .ok config)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (layout : LocalLayout)
    (fuel : Nat) (debugOff : options.place.debugAssertions = false)
    (sized : layout.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (noGhost : machine.user.payload.ghost = false)
    (kind : CompilerFactAdapters.validityKind p.lifecycle.calls.symbols.facts layout.ty =
      .ok (.aggregate false false false))
    (node : TypeNode) (nodeFound : p.lifecycle.calls.symbols.facts.context.runtime.node layout.ty = .ok node)
    (inhabited : CompilerFacts.boolean p.lifecycle.calls.symbols.facts.context layout.ty "opsem_inhabited" = .ok true)
    (fields : layout.layout.fields = .Arbitrary #[] #[])
    (variants : layout.layout.variants = .Single 0) :
    ValidityVisitor.validatePlace config.validity () (fuel+1) (BodyStep.destination frames frame layout) false true
      (BodyStep.current frames (BodyStep.withUnit frame .uninit (some layout)) machine) =
      .ok () (BodyStep.current frames (BodyStep.withUnit frame .uninit (some layout)) machine) := by
  have methods := BodyDictionaries.fields_of_make p image bytes options leaves remaining contract config built
  have classifyEq : config.validity.classify =
      (CompilerFactAdapters.validityHooks p.lifecycle.calls.symbols.facts config.validity).classify :=
    congrArg BodyDictionaries.Queries.classify methods
  have nameEq : config.validity.typeName =
      (CompilerFactAdapters.validityHooks p.lifecycle.calls.symbols.facts config.validity).typeName :=
    congrArg BodyDictionaries.Queries.typeName methods
  have inhabitedEq : config.validity.opsemInhabited =
      (CompilerFactAdapters.validityHooks p.lifecycle.calls.symbols.facts config.validity).opsemInhabited :=
    congrArg BodyDictionaries.Queries.inhabited methods
  have ghostEq : @config.validity.withGhostValidation =
      @ValidityMachine.withGhostValidation MiriMemoryKind
        (EvalCoreMachine.Stored Unit Unit Unit Unit Unit Unit Unit Unit MinimalHost) :=
    congrArg (fun q => @q.ghost) methods
  have debugEq : config.validity.debugAssertions = options.place.debugAssertions :=
    congrArg BodyDictionaries.Queries.debug methods
  apply BodyValidation.shallow_fieldless config.validity () fuel _ _ node.display noGhost ghostEq
  · rw [nameEq]
    exact BodyQueries.adapter_name _ _ () _ _ node nodeFound
  · have read := BodyDictionaries.read_of_make p image bytes options leaves remaining contract config built
      frames frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
      layout debugOff sized noClocks
    simpa only [BodyValidation.active, BodyStep.current, LocalUnit.current, BodyStep.destination] using read
  · rw [classifyEq]
    exact BodyQueries.adapter_classifier _ _ () _ _ kind
  · rw [inhabitedEq]
    exact BodyQueries.adapter_inhabited _ _ () _ _ inhabited
  · exact fields
  · exact variants
  · exact debugEq.trans debugOff

end EmptyFunction.BodyCanonicalValidation
