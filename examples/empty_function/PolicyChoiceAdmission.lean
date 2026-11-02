import empty_function.ChoiceAdmission
import empty_function.PolicyChoiceSupply
namespace EmptyFunction.SourceChoicePlan
open WholeCall
set_option autoImplicit false
/-- The actual source-derived grammar interpreted on supplied or generated
policy responses. No policy, seed or terminal-cursor restriction is imposed. -/
def PolicyEnvironment {s : Static} {before : State}
    {source : Miri.Memory.Allocation Miri.Memory.CtfeProvenance Unit}
    (binding : Binding s before source) : Prop :=
  PolicyChoiceSupply.Environment (actualPlan binding) before.machine.user.payload.payload.user.choices

def ProjectedPolicyEnvironment {s : Static} {p : Packet} (binding : ProjectedBinding s p) : Prop :=
  PolicyChoiceSupply.Environment (projectedPlan binding) p.before.machine.user.payload.payload.user.choices
end EmptyFunction.SourceChoicePlan
namespace EmptyFunction.PolicyChoiceAdmission
open WholeCall
set_option autoImplicit false
/-- Environmental adequacy uses actual policy bookkeeping at every requested
site. Non-choice halts are not filtered out by this condition. -/
structure Environment (s : Static) (p : Packet) : Prop where
  latent : ∀ id source, ChoiceAdmission.SelectedSource s p id source →
    ∃ binding : SourceChoicePlan.Binding s p.before source, SourceChoicePlan.PolicyEnvironment binding
  projected : InputDraft.NeedsEnclosingAllocation p →
    ∃ binding : SourceChoicePlan.ProjectedBinding s p, SourceChoicePlan.ProjectedPolicyEnvironment binding
end EmptyFunction.PolicyChoiceAdmission
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if ["EmptyFunction.SourceChoicePlan.PolicyEnvironment","EmptyFunction.SourceChoicePlan.ProjectedPolicyEnvironment",
        "EmptyFunction.PolicyChoiceAdmission."].any (fun label => name.toString.startsWith label) then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved policy admission axiom {dependency} in {name}"
