import duplicate_prefix.GuardCompilerFacts
import duplicate_prefix.CopyRuntimeCallFacts
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
  (PreparedReflection.actual.runtime.lookup 243).toOption.getD RootCompilerFacts.boolLayout

theorem functionLayout_query : PreparedReflection.actual.runtime.lookup 243 = .ok functionLayout := by
  decide +kernel

theorem functionLayout_shape : functionLayout.ty = 243 ∧ functionLayout.layout.isSized = true ∧
    functionLayout.layout.isZst = true := by
  decide +kernel

theorem function_kind : CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions 243 =
    .ok (.FnDef 24 #[]) := by
  with_unfolding_all rfl

def rustExternAbiJson : Lean.Json := Lean.Json.mkObj
  [("source_spelling", Lean.Json.str "Rust"), ("kind", Lean.Json.str "rust"),
   ("status", Lean.Json.str "supported"), ("unwind", Lean.Json.null)]

theorem function_signature_query : CompilerFunctionFacts.signature
    PreparedReflection.actual.compiler.functions 243 = .ok (0, rustExternAbiJson) := by
  with_unfolding_all rfl

theorem decode_rust_extern_abi (cmp : ProjectionMetadataFacts.NullComparator) :
    CompilerExternAbi.decode rustExternAbiJson = .ok .Rust := by
  have status : rustExternAbiJson.getObjVal? "status" = .ok (.str "supported") := by
    with_unfolding_all rfl
  have unwind : rustExternAbiJson.getObjVal? "unwind" = .ok .null := by
    with_unfolding_all rfl
  have kind : rustExternAbiJson.getObjVal? "kind" = .ok (.str "rust") := by
    with_unfolding_all rfl
  unfold CompilerExternAbi.decode
  change (Lean.Json.null == Lean.Json.null) = true at cmp
  simp [status, unwind, kind, cmp, bind, Except.bind, pure, Except.pure, Lean.Json.getStr?]

theorem runtime_function_type_id :
    (GuardCompilerFacts.runtimeCall.source.getObjVal? "function_type").bind
      (fun fnType => (fnType.getObjVal? "type_id").bind Lean.Json.getNat?) = .ok 243 := by
  with_unfolding_all rfl

theorem function_abi : CompilerInstanceAbi.abiOfInstance
    PreparedReflection.actual.compiler.lifecycle.instances GuardCompilerFacts.runtimeCall.callee #[] =
      .ok GuardCompilerFacts.runtimeAbi := by
  exact GuardCompilerFacts.runtime_abi_eq

theorem function_body : CallResolution.loadedBodyOfInstance
    PreparedReflection.actual.compiler.lifecycle.calls.calls GuardCompilerFacts.runtimeCall.callee =
      .ok CopyPreconditions.Bodies.languageRuntime.loaded := by
  exact GuardCompilerFacts.runtime_body_eq

theorem function_kind_matches_call : GuardCompilerFacts.runtimeCall.callee = ⟨.Item 24, #[]⟩ := by
  exact GuardCompilerFacts.runtime_callee

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
    CompilerProviders.resolveCurrent PreparedReflection.actual.compiler 24 #[]
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
#print axioms DuplicatePrefix.RuntimeCallQueries.decode_rust_extern_abi
