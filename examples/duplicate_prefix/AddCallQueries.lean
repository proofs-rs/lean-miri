import duplicate_prefix.AddFunctionFacts
import duplicate_prefix.ResolveCurrentMetadata
namespace DuplicatePrefix.AddCallQueries
open Miri Miri.ABI Miri.Input Miri.Memory Miri.MIR Miri.Interpreter
open AddFunctionFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
theorem resolve_current
    (framesBefore : Array (Frame Miri.Memory.Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (function : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨7,13⟩) :
    CompilerProviders.resolveCurrent PreparedReflection.actual.compiler 4 HelperCompilerFacts.addCall.callee.args
      (Storage.withCurrent framesBefore frame machine) =
      .ok HelperCompilerFacts.addCall.callee (Storage.withCurrent framesBefore frame machine) := by
  obtain ⟨input,sourceAt,sameInput⟩ := Option.map_eq_some_iff.mp PreparedContracts.fixed_root_body
  have sourceAtFrame : PreparedReflection.actual.compiler.program.bundle.bodies[frame.bodyIdentity.index]? = some input := by
    have program : PreparedReflection.actual.compiler.program = PreparedReflection.actual.program :=
      PreparedReflection.prepared_program
    rw [program,identity]
    exact sourceAt
  have blockBound : 7 < RootBody.reflected.body.body.basicBlocks.size := by decide +kernel
  let block := RootBody.reflected.body.body.basicBlocks[7]'blockBound
  have blockAt : input.body.basicBlocks[7]? = some block := by
    rw [sameInput]
    exact Array.getElem?_eq_getElem blockBound
  have atEnd : (13 : Nat) = block.statements.size := by with_unfolding_all rfl
  have id : HelperCompilerFacts.addCall.callee.defId = 4 := by with_unfolding_all rfl
  have kind : CompilerFunctionFacts.kind PreparedReflection.actual.compiler.functions 30 =
      .ok (.FnDef 4 HelperCompilerFacts.addCall.callee.args) := by
    simpa only [id] using function_kind
  apply ResolveCurrentMetadata.resolve PreparedReflection.actual.compiler framesBefore frame machine ⟨7,13⟩
    input RootBody.reflected.body block HelperCompilerFacts.addCall 4 HelperCompilerFacts.addCall.callee.args 30
    location sourceAtFrame
  · exact sameInput.trans body.symm
  · rw [function]
    exact PreparedContracts.fixed_root_loaded
  · exact identity.symm
  · exact blockAt
  · exact atEnd
  · rw [identity]
    exact HelperCompilerFacts.add_call_eq
  · exact runtime_function_type_id
  · exact kind
  · simp

#print axioms resolve_current
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``resolve_current) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved asmut resolution dependency {dependency}"
end DuplicatePrefix.AddCallQueries
