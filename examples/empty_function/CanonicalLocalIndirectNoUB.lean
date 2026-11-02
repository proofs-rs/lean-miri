import empty_function.CanonicalLocalQuery
namespace EmptyFunction.CanonicalLocalIndirectNoUB
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem noUB (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (destination : InputDraft.LocalDestination s p input.tracker)
    (old : MemPlace Provenance) (indirect : destination.oldOperand = .indirect old) : CallLevelNoUB.NoUB s p := by
  apply LocalIndirectPhasesNoUB.noUB s metadata profile p runtime input destination old indirect
  · exact CanonicalLocalProtection.outcome s metadata profile p runtime input destination old indirect
  · intro entry borrow changed
    dsimp only
    intro actual amount projected positive
    exact CanonicalLocalProtection.query s metadata profile p runtime input destination old indirect entry
      borrow changed actual amount projected positive
end EmptyFunction.CanonicalLocalIndirectNoUB
