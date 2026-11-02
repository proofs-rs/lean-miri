import empty_function.CanonicalMemoryNoUB
import empty_function.CanonicalLocalIndirectNoUB
import empty_function.LocalImmediateNoUB
import empty_function.ProjectedImmediateNoUB
import empty_function.TotalCallGoal
namespace EmptyFunction.ActualNoUBFinal
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Every agreed valid current caller is observed through actual initialization
and every finite in-call prefix. Resource failures may stop execution safely. -/
theorem noUB (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p) :
    CallLevelNoUB.NoUB s p := by
  rcases input.destination with localInput | memoryInput
  · obtain ⟨destination⟩ := localInput
    cases old : destination.oldOperand with
    | indirect memory =>
      exact CanonicalLocalIndirectNoUB.noUB s metadata profile p runtime input destination memory old
    | immediate value =>
      cases offset : destination.offset with
      | none => exact LocalImmediateNoUB.noUB s metadata profile p runtime input destination offset value old
      | some amount => exact ProjectedImmediateNoUB.noUB s metadata profile p runtime input destination amount offset value old
  · obtain ⟨destination⟩ := memoryInput
    exact CanonicalMemoryNoUB.noUB s metadata profile p runtime input destination

/-- The original resource-independent target, with no remaining family or
future operation-success obligations in its statement. -/
theorem target (s : Static) : TotalCallGoal.Target s := by
  intro metadata profile p valid
  obtain ⟨metadata⟩ := metadata
  rcases valid with ⟨runtime,⟨input⟩⟩
  exact noUB s metadata profile p runtime input
end EmptyFunction.ActualNoUBFinal
