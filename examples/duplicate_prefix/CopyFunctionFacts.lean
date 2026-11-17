import duplicate_prefix.CopyCallFacts
import duplicate_prefix.MetadataCallQueries
import duplicate_prefix.ProjectionMetadataFacts


namespace DuplicatePrefix.CopyFunctionFacts
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
open DuplicatePrefix
open Lean Elab Tactic

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

noncomputable def functionLayout : LocalLayout :=
  ((PreparedReflection.actual.layoutResults[31]'(by decide +kernel))).toOption.getD RootCompilerFacts.boolLayout

theorem functionLayout_query : PreparedReflection.actual.runtime.lookup 31 = .ok functionLayout := by decide +kernel

theorem functionLayout_shape : functionLayout.ty = 31 ∧ functionLayout.layout.isSized = true ∧
    functionLayout.layout.isZst = true := by
  decide +kernel

theorem function_kind : CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions 31 =
    .ok (.FnDef (PreparedReflection.fixedInstance HelperCompilerFacts.copyCall.callee).instanceKind.defId (PreparedReflection.fixedInstance HelperCompilerFacts.copyCall.callee).genericArgs) := by
  with_unfolding_all rfl

def rustExternAbi : ABI.ExternAbi := .Rust

theorem function_signature_query : CompilerFunctionFacts.signature
    PreparedReflection.actual.compiler.functions 31 = .ok (3, rustExternAbi) := by
  with_unfolding_all rfl

theorem runtime_function_type_id :
    HelperCompilerFacts.copyCall.source.functionType = some 31 := by
  with_unfolding_all rfl

theorem function_abi : CompilerInstanceAbi.abiOfInstance
    PreparedReflection.actual.compiler.lifecycle.instances HelperCompilerFacts.copyCall.callee #[] =
      .ok HelperCompilerFacts.copyAbi := by
  exact HelperCompilerFacts.copy_abi_eq

theorem function_body : CallResolution.loadedBodyOfInstance
    PreparedReflection.actual.compiler.lifecycle.calls.calls HelperCompilerFacts.copyCall.callee =
      .ok HelperCompilerFacts.copyBody := by
  exact HelperCompilerFacts.copy_body_eq

theorem function_kind_matches_call : (PreparedReflection.fixedInstance HelperCompilerFacts.copyCall.callee).instanceKind =
    .Item (PreparedReflection.fixedInstance HelperCompilerFacts.copyCall.callee).instanceKind.defId := by
  with_unfolding_all rfl

theorem root_bundle_body :
    (PreparedReflection.actual.compiler.program.bundle.bodies[
      RootBody.reflected.body.identity.index]?).map (·.body) =
      some RootBody.reflected.body.body := by
  with_unfolding_all rfl


end DuplicatePrefix.CopyFunctionFacts

open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.CopyFunctionFacts.functionLayout_query,
      ``DuplicatePrefix.CopyFunctionFacts.functionLayout_shape, ``DuplicatePrefix.CopyFunctionFacts.function_kind,
      ``DuplicatePrefix.CopyFunctionFacts.function_signature_query, ``DuplicatePrefix.CopyFunctionFacts.runtime_function_type_id, ``DuplicatePrefix.CopyFunctionFacts.function_abi,
      ``DuplicatePrefix.CopyFunctionFacts.function_body, ``DuplicatePrefix.CopyFunctionFacts.function_kind_matches_call,
      ``DuplicatePrefix.CopyFunctionFacts.root_bundle_body] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved copy function fact {dependency}"
