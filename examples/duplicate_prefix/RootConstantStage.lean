import duplicate_prefix.RootCompilerFacts
import duplicate_prefix.Storage
import duplicate_prefix.ConstantValueProof
import Miri.Interpreter.ConstantMachine

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace DuplicatePrefix.RootConstantStage
open Miri Miri.ABI Miri.Input Miri.MIR Miri.Interpreter Miri.Memory

def zeroConstant : ConstOperand := ⟨⟨25⟩, none, .Val (.Scalar (.Int 0 8)) 5⟩

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
    ConstantMachine.evalOperandWithLayout PreparedReflection.actual.compiler.runtime functions arithmetic externStatic MemoryErrors.constant
      ⟨⟨25⟩, none, .Val (.Scalar (.Int 0 8)) 5⟩ (some RootCompilerFacts.usizeLayout) none
      (Storage.withCurrent framesBefore frame machine) =
    .ok ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 0))),
      RootCompilerFacts.usizeLayout⟩ (Storage.withCurrent framesBefore frame machine) := by
  simp only [ConstantMachine.evalOperandWithLayout, ConstantMachine.evalValueWithLayout, Option.map_none]
  rw [ConstantValueProof.scalar_zero]

#print axioms zero_eval_at_bound
end DuplicatePrefix.RootConstantStage
