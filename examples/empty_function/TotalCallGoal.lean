import empty_function.CallLevelNoUB
import empty_function.Specification
namespace EmptyFunction.TotalCallGoal
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false

/-- The original UB-freedom goal. All actual initialization errors and all
in-call finite-prefix errors are observed; safe exhaustion is allowed.
No numeric margin, supported-choice premise, successful return, or NoErrors
assumption restricts the admitted current callers. This definition is a goal;
its semantic initialization/step obligations are discharged by ActualNoUBFinal.target. -/
def Target (s : Static) : Prop :=
  CallLevelNoUB.Target s (Nonempty (Metadata s)) (Profile s)
    (fun p => RuntimeProfile s p ∧ Nonempty (InputDraft.CurrentInputDraft s p))

end EmptyFunction.TotalCallGoal
