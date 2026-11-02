import empty_function.PushedProfile
import empty_function.ProtectionOutcome
namespace EmptyFunction.PushedSnapshot
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false

theorem fields (s : Static) (metadata : Metadata s) (before : ProtectionOutcome.Machine)
    (frames : Array LocalUnit.F) (frame previous : LocalUnit.F) :
    (PushedProfile.machine s before frames frame previous).memory = before.memory ∧
    (PushedProfile.machine s before frames frame previous).user.addresses = before.user.addresses ∧
    (PushedProfile.machine s before frames frame previous).user.payload.payload.user.runtime =
      before.user.payload.payload.user.runtime := by
  unfold PushedProfile.machine FrameRelevance.pushedMachine
  rw [(MetadataBinding.fields s metadata (InitializationPrefix.capacity_positive s)).freshLocalsIdentity]
  split <;>exact ⟨rfl,rfl,rfl⟩
end EmptyFunction.PushedSnapshot
