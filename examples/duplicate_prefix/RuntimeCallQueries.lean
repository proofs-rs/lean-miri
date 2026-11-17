import duplicate_prefix.GuardCompilerFacts
import duplicate_prefix.ProjectionMetadataFacts

/-! Concrete compiler leaves used to evaluate check_language_ub's zero-argument
runtime guard call. -/
namespace DuplicatePrefix.RuntimeCallQueries
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter
open DuplicatePrefix
open Lean Elab Tactic

private def providerLiftName : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".CompilerProviders.lift" then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected unique CompilerProviders.lift helper"

elab "unfold_provider_lift" : tactic => do
  let name := mkIdent (← providerLiftName)
  evalTactic (← `(tactic| unfold $name:ident))
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

noncomputable def functionLayout : LocalLayout :=
  ((PreparedReflection.actual.layoutResults[127]'(by decide +kernel))).toOption.getD RootCompilerFacts.boolLayout

theorem functionLayout_query : PreparedReflection.actual.runtime.lookup 127 = .ok functionLayout := by decide +kernel

theorem functionLayout_shape : functionLayout.ty = 127 ∧ functionLayout.layout.isSized = true ∧
    functionLayout.layout.isZst = true := by
  decide +kernel

theorem function_kind : CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions 127 =
    .ok (.FnDef (PreparedReflection.fixedInstance GuardCompilerFacts.runtimeCall.callee).instanceKind.defId #[]) := by
  with_unfolding_all rfl

def rustExternAbi : ABI.ExternAbi := .Rust

theorem function_signature_query : CompilerFunctionFacts.signature
    PreparedReflection.actual.compiler.functions 127 = .ok (0, rustExternAbi) := by
  with_unfolding_all rfl

theorem runtime_function_type_id :
    GuardCompilerFacts.runtimeCall.source.functionType = some 127 := by
  with_unfolding_all rfl

theorem function_abi : CompilerInstanceAbi.abiOfInstance
    PreparedReflection.actual.compiler.lifecycle.instances GuardCompilerFacts.runtimeCall.callee #[] =
      .ok GuardCompilerFacts.runtimeAbi := by
  exact GuardCompilerFacts.runtime_abi_eq

theorem function_body : CallResolution.loadedBodyOfInstance
    PreparedReflection.actual.compiler.lifecycle.calls.calls GuardCompilerFacts.runtimeCall.callee =
      .ok CopyPreconditions.Bodies.languageRuntime.loaded := by
  exact GuardCompilerFacts.runtime_body_eq

theorem function_kind_matches_call : (PreparedReflection.fixedInstance GuardCompilerFacts.runtimeCall.callee).instanceKind =
    .Item (PreparedReflection.fixedInstance GuardCompilerFacts.runtimeCall.callee).instanceKind.defId := by
  with_unfolding_all rfl

theorem check_language_bundle_body :
    (PreparedReflection.actual.compiler.program.bundle.bodies[
      CopyPreconditions.Bodies.checkLanguage.loaded.identity.index]?).map (·.body) =
      some CopyPreconditions.Bodies.checkLanguage.loaded.body := by
  with_unfolding_all rfl

theorem resolve_current
    (framesBefore : Array (Frame Miri.Memory.Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (function : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : frame.location = .mir ⟨0,3⟩) :
    CompilerProviders.resolveCurrent PreparedReflection.actual.compiler (PreparedReflection.fixedInstance GuardCompilerFacts.runtimeCall.callee).instanceKind.defId #[]
      (Storage.withCurrent framesBefore frame machine) =
      .ok GuardCompilerFacts.runtimeCall.callee (Storage.withCurrent framesBefore frame machine) := by
  unfold CompilerProviders.resolveCurrent
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [body, identity, function, location]
  unfold_provider_lift
  with_unfolding_all rfl

end DuplicatePrefix.RuntimeCallQueries

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.RuntimeCallQueries.functionLayout_query,
      ``DuplicatePrefix.RuntimeCallQueries.functionLayout_shape,
      ``DuplicatePrefix.RuntimeCallQueries.function_kind,
      ``DuplicatePrefix.RuntimeCallQueries.function_signature_query,
      ``DuplicatePrefix.RuntimeCallQueries.function_abi,
      ``DuplicatePrefix.RuntimeCallQueries.function_body,
      ``DuplicatePrefix.RuntimeCallQueries.function_kind_matches_call] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved dependency {dependency} in {declaration}"

#print axioms DuplicatePrefix.RuntimeCallQueries.resolve_current
