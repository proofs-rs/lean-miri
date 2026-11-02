import duplicate_prefix.S05ZeroCellJointPacket
import duplicate_prefix.ActualReferenceContext

/-! One fixed call only: len=2, count=1, and the closed joint packet.
This file only binds the exact actual configuration, operand encoding and
initial-call expression to the retained Result parameters. It proves no
execution step, call success, error, NoErrors violation or NoUB violation. -/
namespace DuplicatePrefix.S05ZeroCellActualCallParameters
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

abbrev State := MachineHooks.State MiriMemoryKind Machine.RootUser
abbrev Config := ExecutionMachine.Config MiriMemoryKind Machine.RootUser Unit Unit ABI.ExternAbi Unit

def budget : Nat := 1000000
def remaining : Nat := 999999
def limits : ExecutionMachine.Limits := ⟨budget,budget,budget,budget⟩
def options : EvalConfigurationCore.Options :=
  Machine.exampleOptions limits budget budget budget 64 .Shallow ⟨false,false⟩

theorem capacity : remaining + 2 = 1000001 := rfl

/-- The error branch is unreachable by `actualConfig_eq`; keeping it as
ordinary data avoids a dependent extraction proof during source reduction. -/
noncomputable def configuration (span : PreparedContracts.FixedSpanQuery) : Config :=
  match Machine.actualConfig options () (remaining+2) with
  | .ok cfg => cfg
  | .error _ => ActualReferenceContext.config options (remaining+1) span

theorem configuration_exact (span : PreparedContracts.FixedSpanQuery) :
    configuration span = ActualReferenceContext.config options (remaining+1) span := by
  unfold configuration
  rw [PreparedContracts.actualConfig_eq options () (remaining+1) span]

theorem configuration_source (span : PreparedContracts.FixedSpanQuery) :
    Machine.actualConfig options () (remaining+2) = .ok (configuration span) := by
  rw [configuration_exact]
  exact PreparedContracts.actualConfig_eq options () (remaining+1) span

theorem first_base (span : PreparedContracts.FixedSpanQuery) :
    (ActualReferenceContext.config options remaining span).access.runtime.base =
      PreparedReflection.actual.runtime.target.base := by
  rw [CanonicalConfigFacts.actual_access_runtime]

noncomputable def initializationResult (span : PreparedContracts.FixedSpanQuery) :
    EStateM.Result StepError State Unit :=
  Call.initStackFrame (ExecutionMachine.callHooks (configuration span) limits) ()
    RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
    #[.Copy (DuplicatePrefixSliceArgument.first PreparedReflection.actual.runtime.target.base
        S05ZeroCellJointPacket.argument 2), .Copy (EmptyRootArguments.second 1)]
    false (.memory S05ZeroCellJointPacket.place) (.stop true) S05ZeroCellJointPacket.state

theorem initializationResult_exact (span : PreparedContracts.FixedSpanQuery) :
    initializationResult span =
    Call.initStackFrame (ExecutionMachine.callHooks (ActualReferenceContext.config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (ActualReferenceContext.config options remaining span).access.runtime.base
          S05ZeroCellJointPacket.argument 2), .Copy (EmptyRootArguments.second 1)]
      false (.memory S05ZeroCellJointPacket.place) (.stop true) ⟨⟨#[]⟩,S05ZeroCellJointPacket.before⟩ := by
  rw [initializationResult,configuration_exact,first_base]
  rfl

/-- Unit choices in the retained Result are admitted unconditionally. -/
theorem unit_choice_permitted (state : State) : (fun (_ : State) (_ : Unit) => True) state () := trivial

end DuplicatePrefix.S05ZeroCellActualCallParameters
