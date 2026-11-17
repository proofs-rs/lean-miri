import duplicate_prefix.AddCallFacts
import duplicate_prefix.MetadataCallQueries
import duplicate_prefix.ProjectionMetadataFacts

/-! Concrete compiler leaves used to evaluate check_language_ub's zero-argument
runtime guard call. -/
namespace DuplicatePrefix.AddFunctionFacts
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
open DuplicatePrefix
open Lean Elab Tactic

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

noncomputable def functionLayout : LocalLayout :=
  ((PreparedReflection.actual.layoutResults[30]'(by decide +kernel))).toOption.getD RootCompilerFacts.boolLayout

theorem functionLayout_query : PreparedReflection.actual.runtime.lookup 30 = .ok functionLayout := by decide +kernel

theorem functionLayout_shape : functionLayout.ty = 30 ∧ functionLayout.layout.isSized = true ∧
    functionLayout.layout.isZst = true := by
  decide +kernel

theorem function_kind : CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions 30 =
    .ok (.FnDef (PreparedReflection.fixedInstance HelperCompilerFacts.addCall.callee).instanceKind.defId (PreparedReflection.fixedInstance HelperCompilerFacts.addCall.callee).genericArgs) := by
  with_unfolding_all rfl

def rustExternAbi : ABI.ExternAbi := .Rust

theorem function_signature_query : CompilerFunctionFacts.signature
    PreparedReflection.actual.compiler.functions 30 = .ok (2, rustExternAbi) := by
  with_unfolding_all rfl

theorem runtime_function_type_id :
    HelperCompilerFacts.addCall.source.functionType = some 30 := by
  with_unfolding_all rfl

theorem function_abi : CompilerInstanceAbi.abiOfInstance
    PreparedReflection.actual.compiler.lifecycle.instances HelperCompilerFacts.addCall.callee #[] =
      .ok HelperCompilerFacts.addAbi := by
  exact HelperCompilerFacts.add_abi_eq

theorem function_body : CallResolution.loadedBodyOfInstance
    PreparedReflection.actual.compiler.lifecycle.calls.calls HelperCompilerFacts.addCall.callee =
      .ok HelperCompilerFacts.addBody := by
  exact HelperCompilerFacts.add_body_eq

theorem function_kind_matches_call : (PreparedReflection.fixedInstance HelperCompilerFacts.addCall.callee).instanceKind =
    .Item (PreparedReflection.fixedInstance HelperCompilerFacts.addCall.callee).instanceKind.defId := by
  with_unfolding_all rfl

theorem root_bundle_body :
    (PreparedReflection.actual.compiler.program.bundle.bodies[
      RootBody.reflected.body.identity.index]?).map (·.body) =
      some RootBody.reflected.body.body := by
  with_unfolding_all rfl


end DuplicatePrefix.AddFunctionFacts
