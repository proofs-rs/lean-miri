import duplicate_prefix.AsMutCallFacts
import duplicate_prefix.MetadataCallQueries
import duplicate_prefix.ProjectionMetadataFacts

/-! Concrete compiler leaves used to evaluate check_language_ub's zero-argument
runtime guard call. -/
namespace DuplicatePrefix.AsMutFunctionFacts
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
open DuplicatePrefix
open Lean Elab Tactic

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

noncomputable def functionLayout : LocalLayout :=
  ((PreparedReflection.actual.layoutResults[28]'(by decide +kernel))).toOption.getD RootCompilerFacts.boolLayout

theorem functionLayout_query : PreparedReflection.actual.runtime.lookup 28 = .ok functionLayout := by decide +kernel

theorem functionLayout_shape : functionLayout.ty = 28 ∧ functionLayout.layout.isSized = true ∧
    functionLayout.layout.isZst = true := by
  decide +kernel

theorem function_kind : CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions 28 =
    .ok (.FnDef (PreparedReflection.fixedInstance HelperCompilerFacts.asMutPtrCall.callee).instanceKind.defId (PreparedReflection.fixedInstance HelperCompilerFacts.asMutPtrCall.callee).genericArgs) := by
  with_unfolding_all rfl

def rustExternAbi : ABI.ExternAbi := .Rust

theorem function_signature_query : CompilerFunctionFacts.signature
    PreparedReflection.actual.compiler.functions 28 = .ok (1, rustExternAbi) := by
  with_unfolding_all rfl

theorem runtime_function_type_id :
    HelperCompilerFacts.asMutPtrCall.source.functionType = some 28 := by
  with_unfolding_all rfl

theorem function_abi : CompilerInstanceAbi.abiOfInstance
    PreparedReflection.actual.compiler.lifecycle.instances HelperCompilerFacts.asMutPtrCall.callee #[] =
      .ok HelperCompilerFacts.asMutPtrAbi := by
  exact HelperCompilerFacts.as_mut_ptr_abi_eq

theorem function_body : CallResolution.loadedBodyOfInstance
    PreparedReflection.actual.compiler.lifecycle.calls.calls HelperCompilerFacts.asMutPtrCall.callee =
      .ok HelperCompilerFacts.asMutPtrBody := by
  exact HelperCompilerFacts.as_mut_ptr_body_eq

theorem function_kind_matches_call : (PreparedReflection.fixedInstance HelperCompilerFacts.asMutPtrCall.callee).instanceKind =
    .Item (PreparedReflection.fixedInstance HelperCompilerFacts.asMutPtrCall.callee).instanceKind.defId := by
  with_unfolding_all rfl

theorem root_bundle_body :
    (PreparedReflection.actual.compiler.program.bundle.bodies[
      RootBody.reflected.body.identity.index]?).map (·.body) =
      some RootBody.reflected.body.body := by
  with_unfolding_all rfl


end DuplicatePrefix.AsMutFunctionFacts
