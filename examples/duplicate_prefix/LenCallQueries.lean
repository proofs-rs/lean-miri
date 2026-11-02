import duplicate_prefix.LenCallFacts
import duplicate_prefix.SliceLenFacts
import duplicate_prefix.ProjectionMetadataFacts

/-! Compiler leaves for the root call to the slice-length helper. -/
namespace DuplicatePrefix.LenCallQueries
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
  (PreparedReflection.actual.runtime.lookup 10).toOption.getD RootCompilerFacts.boolLayout

theorem functionLayout_query : PreparedReflection.actual.runtime.lookup 10 = .ok functionLayout := by
  decide +kernel

theorem functionLayout_shape : functionLayout.ty = 10 ∧ functionLayout.layout.isSized = true ∧
    functionLayout.layout.isZst = true := by
  decide +kernel

theorem function_kind : CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions 10 =
    .ok (.FnDef 1 LenHelper.resolved.callee.args) := by
  with_unfolding_all rfl

def rustExternAbiJson : Lean.Json := Lean.Json.mkObj
  [("source_spelling", Lean.Json.str "Rust"), ("kind", Lean.Json.str "rust"),
   ("status", Lean.Json.str "supported"), ("unwind", Lean.Json.null)]

theorem function_signature_query : CompilerFunctionFacts.signature
    PreparedReflection.actual.compiler.functions 10 = .ok (1, rustExternAbiJson) := by
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
    (LenHelper.resolved.source.getObjVal? "function_type").bind
      (fun fnType => (fnType.getObjVal? "type_id").bind Lean.Json.getNat?) = .ok 10 := by
  with_unfolding_all rfl

theorem function_abi : CompilerInstanceAbi.abiOfInstance
    PreparedReflection.actual.compiler.lifecycle.instances LenHelper.resolved.callee #[] =
      .ok LenHelper.abi := by
  exact LenHelper.abi_eq

theorem function_body : CallResolution.loadedBodyOfInstance
    PreparedReflection.actual.compiler.lifecycle.calls.calls LenHelper.resolved.callee =
      .ok LenHelper.body := by
  exact LenHelper.body_eq

theorem function_kind_matches_call : LenHelper.resolved.callee = ⟨.Item 1, LenHelper.resolved.callee.args⟩ := by
  with_unfolding_all rfl

theorem len_bundle_body :
    (PreparedReflection.actual.compiler.program.bundle.bodies[
      RootBody.reflected.body.identity.index]?).map (·.body) =
      some RootBody.reflected.body.body := by
  with_unfolding_all rfl

theorem resolve_current
    (framesBefore : Array (Frame Miri.Memory.Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (function : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨2,12⟩) :
    CompilerProviders.resolveCurrent PreparedReflection.actual.compiler 1 LenHelper.resolved.callee.args
      (Storage.withCurrent framesBefore frame machine) =
      .ok LenHelper.resolved.callee (Storage.withCurrent framesBefore frame machine) := by
  unfold CompilerProviders.resolveCurrent
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [body, identity, function, location]
  have currentLoaded : CallResolution.loadedBodyOfInstance
      PreparedReflection.actual.compiler.lifecycle.calls.calls
      RootBody.reflected.functionInstance =
      .ok RootBody.reflected.body := by
    with_unfolding_all rfl
  have site : CallResolution.atSite PreparedReflection.actual.compiler.lifecycle.calls.calls
      ⟨RootBody.reflected.body.identity.index, 2⟩ =
      .ok LenHelper.resolved := by
    exact HelperCompilerFacts.len_call_eq
  have bundleBody := len_bundle_body
  have hsize : (RootBody.reflected.body.body.basicBlocks[2]?).map
      (fun b => b.statements.size) = some 12 := by
    with_unfolding_all rfl
  have bodyBeq : (RootBody.reflected.body.body ==
      RootBody.reflected.body.body) = true := by simp
  have identityBeq : (RootBody.reflected.body.identity ==
      RootBody.reflected.body.identity) = true := by simp
  simp only [location]
  cases hBundle : (PreparedReflection.actual.compiler.program.bundle.bodies[
      RootBody.reflected.body.identity.index]?) with
  | none => simp [hBundle] at bundleBody
  | some lowered =>
    have loweredBody : lowered.body = RootBody.reflected.body.body := by
      simpa [hBundle] using bundleBody
    have loweredSize : (lowered.body.basicBlocks[2]?).map
        (fun b => b.statements.size) = some 12 := by
      rw [loweredBody]
      exact hsize
    cases hb : lowered.body.basicBlocks[2]? with
    | none => simp [hb] at loweredSize
    | some block =>
      have hs : block.statements.size = 12 := by simpa [hb] using loweredSize
      unfold_provider_lift
      simp_all only [loweredBody, hb, hs, currentLoaded, site, bodyBeq, identityBeq,
        runtime_function_type_id, function_kind, EStateM.bind, EStateM.pure,
        bind,Except.bind,pure,Except.pure,ite_true,beq_self_eq_true]
      simp_all [Except.bind,Except.pure,bind,EStateM.bind,pure,EStateM.pure]
      with_unfolding_all rfl

end DuplicatePrefix.LenCallQueries
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.LenCallQueries.resolve_current, ``DuplicatePrefix.LenCallQueries.decode_rust_extern_abi, ``DuplicatePrefix.LenCallQueries.function_signature_query, ``DuplicatePrefix.LenCallQueries.function_kind] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved metadata callee dependency {dependency}"
