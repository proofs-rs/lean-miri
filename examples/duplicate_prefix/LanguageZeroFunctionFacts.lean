import duplicate_prefix.GuardCompilerFacts
import duplicate_prefix.ProjectionMetadataFacts

/-! Concrete compiler leaves used to evaluate check_language_ub's zero-argument
runtime guard call. -/
namespace DuplicatePrefix.LanguageZeroFunctionFacts
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter
open DuplicatePrefix
open Lean Elab Tactic

private def languageProviderLiftName : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".CompilerProviders.lift" then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected unique CompilerProviders.lift helper"

elab "unfold_languagezero_provider_lift" : tactic => do
  let name := mkIdent (← languageProviderLiftName)
  evalTactic (← `(tactic| unfold $name:ident))
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

noncomputable def functionLayout : LocalLayout :=
  ((PreparedReflection.actual.layoutResults[101]'(by decide +kernel))).toOption.getD RootCompilerFacts.boolLayout

theorem functionLayout_query : PreparedReflection.actual.runtime.lookup 101 = .ok functionLayout := by decide +kernel

theorem functionLayout_shape : functionLayout.ty = 101 ∧ functionLayout.layout.isSized = true ∧
    functionLayout.layout.isZst = true := by
  decide +kernel

theorem function_kind : CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions 101 =
    .ok (.FnDef (PreparedReflection.fixedInstance GuardCompilerFacts.languageCall.callee).instanceKind.defId #[]) := by
  with_unfolding_all rfl

def rustExternAbi : ABI.ExternAbi := .Rust

theorem function_signature_query : CompilerFunctionFacts.signature
    PreparedReflection.actual.compiler.functions 101 = .ok (0, rustExternAbi) := by
  with_unfolding_all rfl

theorem language_function_type_id :
    GuardCompilerFacts.languageCall.source.functionType = some 101 := by
  with_unfolding_all rfl

theorem function_abi : CompilerInstanceAbi.abiOfInstance
    PreparedReflection.actual.compiler.lifecycle.instances GuardCompilerFacts.languageCall.callee #[] =
      .ok GuardCompilerFacts.languageAbi := by
  exact GuardCompilerFacts.language_abi_eq

theorem function_body : CallResolution.loadedBodyOfInstance
    PreparedReflection.actual.compiler.lifecycle.calls.calls GuardCompilerFacts.languageCall.callee =
      .ok CopyPreconditions.Bodies.checkLanguage.loaded := by
  exact GuardCompilerFacts.language_body_eq

theorem function_kind_matches_call : (PreparedReflection.fixedInstance GuardCompilerFacts.languageCall.callee).instanceKind =
    .Item (PreparedReflection.fixedInstance GuardCompilerFacts.languageCall.callee).instanceKind.defId := by
  with_unfolding_all rfl

theorem copy_wrapper_bundle_body :
    (PreparedReflection.actual.compiler.program.bundle.bodies[
      CopyPreconditions.Bodies.copyWrapper.loaded.identity.index]?).map (·.body) =
      some CopyPreconditions.Bodies.copyWrapper.loaded.body := by
  with_unfolding_all rfl

theorem resolve_current
    (framesBefore : Array (Frame Miri.Memory.Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.copyWrapper.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.copyWrapper.loaded.identity)
    (function : frame.functionInstance = CopyPreconditions.Bodies.copyWrapper.fnInstance)
    (location : frame.location = .mir ⟨0,2⟩) :
    CompilerProviders.resolveCurrent PreparedReflection.actual.compiler (PreparedReflection.fixedInstance GuardCompilerFacts.languageCall.callee).instanceKind.defId #[]
      (Storage.withCurrent framesBefore frame machine) =
      .ok GuardCompilerFacts.languageCall.callee (Storage.withCurrent framesBefore frame machine) := by
  unfold CompilerProviders.resolveCurrent
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [body, identity, function, location]
  unfold_languagezero_provider_lift
  with_unfolding_all rfl

end DuplicatePrefix.LanguageZeroFunctionFacts

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.LanguageZeroFunctionFacts.functionLayout_query,
      ``DuplicatePrefix.LanguageZeroFunctionFacts.functionLayout_shape,
      ``DuplicatePrefix.LanguageZeroFunctionFacts.function_kind,
      ``DuplicatePrefix.LanguageZeroFunctionFacts.function_signature_query,
      ``DuplicatePrefix.LanguageZeroFunctionFacts.function_abi,
      ``DuplicatePrefix.LanguageZeroFunctionFacts.function_body,
      ``DuplicatePrefix.LanguageZeroFunctionFacts.function_kind_matches_call] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved dependency {dependency} in {declaration}"

#print axioms DuplicatePrefix.LanguageZeroFunctionFacts.resolve_current
