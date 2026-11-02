import duplicate_prefix.RootCompilerFacts
import duplicate_prefix.Storage
import duplicate_prefix.ConstantValueProof
import Miri.Input.CompilerConstantMachine

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace DuplicatePrefix.RootConstantStage
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory

open Lean Elab Tactic in
elab "simp_root_constant" : tactic => do
  let env ← getEnv
  let found := env.constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith "Miri.Interpreter.constantType"
    then some (mkIdent name) else none
  let names := found.toArray
  evalTactic (← `(tactic| simp_all (config := {maxSteps := 1000000}) [
    CompilerConstantMachine.evalAtBound, ConstantMachine.fromCompiler,
    ConstantMachine.evalOperandWithLayout, evalConstOperandWithLayout,
    evalMirConstantWithLayout, constValueToOpWithLayout,
    ConstantQueries.valueQueries, MachineHooks.currentFrame,
    Storage.withCurrent, Stack.currentFrame?, bind, EStateM.bind,
    get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure,
    Except.bind, Except.pure, RootCompilerFacts.zeroGuardSite,
    ConstantValueProof.scalar_zero, $[$names:ident],*]))

def zeroConstant : ConstOperand := ⟨⟨3⟩, none, .Val (.Scalar (.Int 0 8)) 5⟩

theorem zero_eval_at_bound
    (source : PreparedContracts.SourceComparator)
    (functions : FunctionPointers.Hooks MiriMemoryKind Machine.RootUser Unit)
    (arithmetic : PointerArithmetic)
    (externStatic : DefId → MachineHooks.M MiriMemoryKind Machine.RootUser (Pointer Provenance))
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (bodyIndex : frame.bodyIdentity.index = RootBody.reflected.body.identity.index)
    (location : frame.location = .mir ⟨0, 4⟩)
    (fnInstance : frame.functionInstance = RootBody.reflected.functionInstance) :
    CompilerConstantMachine.evalAtBound PreparedReflection.actual.compiler.constantBinding
      RootCompilerFacts.zeroGuardSite functions arithmetic externStatic MemoryErrors.constant
      ⟨⟨3⟩, none, .Val (.Scalar (.Int 0 8)) 5⟩ (some RootCompilerFacts.usizeLayout) none
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 0))),
      RootCompilerFacts.usizeLayout⟩ (Storage.withCurrent framesBefore frame machine) := by
  have compatible := RootCompilerFacts.constant_binding_compatible source
  have norm : normalizationFromEvidence
      ((PreparedReflection.actual.compiler.constants.evidence.filter
        (·.site == RootCompilerFacts.zeroGuardSite)).map (·.query))
      RootBody.reflected.functionInstance (.Val (.Scalar (.Int 0 8)) 5) =
      .ok (.Val (.Scalar (.Int 0 8)) 5) := by
    simpa [RootCompilerFacts.zeroGuardEvidence, RootCompilerFacts.zeroGuardSite] using
      RootCompilerFacts.zero_guard_normalization
  simp_root_constant

#print axioms zero_eval_at_bound
end DuplicatePrefix.RootConstantStage
