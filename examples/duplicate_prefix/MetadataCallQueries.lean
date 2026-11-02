import duplicate_prefix.MetadataCallFacts
import duplicate_prefix.SliceLenFacts
import duplicate_prefix.ProjectionMetadataFacts

/-! Concrete compiler leaves used to evaluate check_language_ub's zero-argument
runtime guard call. -/
namespace DuplicatePrefix.MetadataCallQueries
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
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
  (PreparedReflection.actual.runtime.lookup 155).toOption.getD RootCompilerFacts.boolLayout

theorem functionLayout_query : PreparedReflection.actual.runtime.lookup 155 = .ok functionLayout := by
  decide +kernel

theorem functionLayout_shape : functionLayout.ty = 155 ∧ functionLayout.layout.isSized = true ∧
    functionLayout.layout.isZst = true := by
  decide +kernel

theorem function_kind : CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions 155 =
    .ok (.FnDef 10 PtrMetadataHelper.resolved.callee.args) := by
  with_unfolding_all rfl

def rustExternAbiJson : Lean.Json := Lean.Json.mkObj
  [("source_spelling", Lean.Json.str "Rust"), ("kind", Lean.Json.str "rust"),
   ("status", Lean.Json.str "supported"), ("unwind", Lean.Json.null)]

theorem function_signature_query : CompilerFunctionFacts.signature
    PreparedReflection.actual.compiler.functions 155 = .ok (1, rustExternAbiJson) := by
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
  simp [status, unwind, kind, cmp,bind,Except.bind,pure,Except.pure,Lean.Json.getStr?]
  exact cmp

theorem runtime_function_type_id :
    (PtrMetadataHelper.resolved.source.getObjVal? "function_type").bind
      (fun fnType => (fnType.getObjVal? "type_id").bind Lean.Json.getNat?) = .ok 155 := by
  with_unfolding_all rfl

theorem function_abi : CompilerInstanceAbi.abiOfInstance
    PreparedReflection.actual.compiler.lifecycle.instances PtrMetadataHelper.resolved.callee #[] =
      .ok PtrMetadataHelper.abi := by
  exact PtrMetadataHelper.abi_eq

theorem function_body : CallResolution.loadedBodyOfInstance
    PreparedReflection.actual.compiler.lifecycle.calls.calls PtrMetadataHelper.resolved.callee =
      .ok PtrMetadataHelper.body := by
  exact PtrMetadataHelper.body_eq

theorem function_kind_matches_call : PtrMetadataHelper.resolved.callee = ⟨.Item 10, PtrMetadataHelper.resolved.callee.args⟩ := by
  with_unfolding_all rfl

theorem len_bundle_body :
    (PreparedReflection.actual.compiler.program.bundle.bodies[
      HelperCompilerFacts.lenBody.identity.index]?).map (·.body) =
      some HelperCompilerFacts.lenBody.body := by
  with_unfolding_all rfl

theorem resolve_current
    (framesBefore : Array (Frame Miri.Memory.Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = HelperCompilerFacts.lenBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.lenBody.identity)
    (function : frame.functionInstance = HelperCompilerFacts.lenCall.callee)
    (location : frame.location = .mir ⟨0,2⟩) :
    CompilerProviders.resolveCurrent PreparedReflection.actual.compiler 10 PtrMetadataHelper.resolved.callee.args
      (Storage.withCurrent framesBefore frame machine) =
      .ok PtrMetadataHelper.resolved.callee (Storage.withCurrent framesBefore frame machine) := by
  unfold CompilerProviders.resolveCurrent
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [body, identity, function, location]
  have currentLoaded : CallResolution.loadedBodyOfInstance
      PreparedReflection.actual.compiler.lifecycle.calls.calls
      HelperCompilerFacts.lenCall.callee =
      .ok HelperCompilerFacts.lenBody := by
    exact HelperCompilerFacts.len_body_eq
  have site : CallResolution.atSite PreparedReflection.actual.compiler.lifecycle.calls.calls
      ⟨HelperCompilerFacts.lenBody.identity.index, 0⟩ =
      .ok PtrMetadataHelper.resolved := by
    exact PtrMetadataHelper.call_eq
  have bundleBody := len_bundle_body
  have hsize : (HelperCompilerFacts.lenBody.body.basicBlocks[0]?).map
      (fun b => b.statements.size) = some 2 := by
    with_unfolding_all rfl
  have bodyBeq : (HelperCompilerFacts.lenBody.body ==
      HelperCompilerFacts.lenBody.body) = true := by decide +kernel
  have identityBeq : (HelperCompilerFacts.lenBody.identity ==
      HelperCompilerFacts.lenBody.identity) = true := by decide +kernel
  simp only [location]
  cases hBundle : (PreparedReflection.actual.compiler.program.bundle.bodies[
      HelperCompilerFacts.lenBody.identity.index]?) with
  | none => simp [hBundle] at bundleBody
  | some lowered =>
    have loweredBody : lowered.body = HelperCompilerFacts.lenBody.body := by
      simpa [hBundle] using bundleBody
    have loweredSize : (lowered.body.basicBlocks[0]?).map
        (fun b => b.statements.size) = some 2 := by
      rw [loweredBody]
      exact hsize
    cases hb : lowered.body.basicBlocks[0]? with
    | none => simp [hb] at loweredSize
    | some block =>
      have hs : block.statements.size = 2 := by simpa [hb] using loweredSize
      unfold_provider_lift
      simp_all only [loweredBody, hb, hs, currentLoaded, site, bodyBeq, identityBeq,
        runtime_function_type_id, function_kind, EStateM.bind, EStateM.pure,
        bind,Except.bind,pure,Except.pure,ite_true,beq_self_eq_true]
      simp_all [Except.bind,Except.pure,bind,EStateM.bind,pure,EStateM.pure]
      with_unfolding_all rfl

end DuplicatePrefix.MetadataCallQueries
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.MetadataCallQueries.resolve_current, ``DuplicatePrefix.MetadataCallQueries.decode_rust_extern_abi, ``DuplicatePrefix.MetadataCallQueries.function_signature_query, ``DuplicatePrefix.MetadataCallQueries.function_kind] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata callee dependency {dependency}"
