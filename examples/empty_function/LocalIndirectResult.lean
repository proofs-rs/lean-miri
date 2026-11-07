import empty_function.LocalIndirectPost
namespace EmptyFunction.LocalIndirectResult
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem result (s : Static) (metadata : Metadata s) [SuccessfulConstant metadata] (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p) (destination : InputDraft.LocalDestination s p input.tracker)
    (whole : destination.offset = none) (place : MemPlace Provenance)
    (indirect : destination.oldOperand = .indirect place)
    (resident : ProtectionDispatch.Resident s p place.ptr) :
    WholeCall.Result s (Preservation.Preserves s) p := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound;omega
  have capacity : 0 < s.capacity := by have bound := resources.capacity;omega
  obtain ⟨older,bound,choice,installed,finish,frame,previous,index,original,installEq,depthEq,
    trace,returned,safe,noub,finished⟩ :=
      LocalIndirectEndpoint.run_operations s metadata profile p runtime input resources destination whole place indirect resident
  have preserved := LocalIndirectPost.preserves s metadata capacity p input.tracker destination older bound frame previous index
    (ConcreteProtection.tag_room s p input resources) choice original whole input.world.enabled
  rw [←finished] at preserved
  exact ⟨installed,finish,installEq,depthEq,trace,returned,preserved,safe,noub⟩
end EmptyFunction.LocalIndirectResult
