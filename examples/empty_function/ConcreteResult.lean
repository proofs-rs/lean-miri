import empty_function.ConcretePost
namespace EmptyFunction.ConcreteResult
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem result (s : Static) (metadata : Metadata s) [SuccessfulConstant metadata] (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p)
    (resources : ResourceMargins s p)
    (destination : InputDraft.MemoryDestination s p input.tracker)
    (id : AllocId) (tag : BorTag)
    (encoding : destination.place.mplace.ptr.provenance = some (.concrete id tag))
    (entry : InputDraft.Entry)
    (live : p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    WholeCall.Result s (Preservation.Preserves s) p := by
  have budget : 64 ≤ resources.budget := by have bound := resources.reserve; unfold work at bound; omega
  have capacity : 0 < s.capacity := by have bound := resources.capacity; omega
  obtain ⟨installed,finish,frame,previous,tree,index,older,original,installEq,depthEq,trace,returned,safe,noub,finished,rights⟩ :=
    ConcreteEndpoint.run_operations s metadata profile p runtime input resources destination id tag encoding entry live
  have preserved := ConcretePost.preserves s metadata capacity p frame previous input.tracker
    (ConcreteProtection.tag_room s p input resources) index older input.caller original input.world.enabled
    destination.place destination.encoding id entry live tree rights
  have preserveFinish : Preservation.Preserves s p finish := by
    rw [finished,ConcretePost.finished_eq]
    exact preserved
  exact ⟨installed,finish,installEq,depthEq,trace,returned,preserveFinish,safe,noub⟩
end EmptyFunction.ConcreteResult
