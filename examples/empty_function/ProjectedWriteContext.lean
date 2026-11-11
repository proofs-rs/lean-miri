import empty_function.ProjectedCreate
namespace EmptyFunction.ProjectedWriteContext
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

theorem registered (s : Static) (state : State)
    (reserved : MemoryState Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (global : GlobalState) (id : AllocId) (bytes : Allocation Provenance Unit) (tag : BorTag) (size : Size)
    (tape : ExecutionChoices.Tape) (addresses : AllocAddresses.GlobalAddressState)
    (backend : state.machine.user.payload.payload.user.backend = .none) (noRace : state.machine.dataRace = none)
    (ghost : state.machine.user.payload.ghost = false) (shallow : state.machine.user.payload.validation = .Shallow) :
    let post := ProjectedAddress.assigned (ChoiceProjection.tapeAccess.put
      (ProjectedCreate.registered s state reserved tracker global id bytes tag size) tape) addresses
    post.machine.user.payload.payload.user.backend = .none ∧ post.machine.dataRace = none ∧
    post.machine.user.payload.ghost = false ∧ post.machine.user.payload.validation = .Shallow ∧
    post.machine.memory.live = reserved.live.push (id,⟨.stack,bytes.withExtra (BorrowTree.new tag size)⟩) ∧
    post.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,{weakMemory := none}) ∧
    post.machine.borrowTracker = some {tracker with global} := by
  dsimp only
  refine ⟨backend,noRace,ghost,shallow,rfl,?_,rfl⟩
  change ((state.machine.user.payload.payload.user.runtime.extras.allocations.filter (fun row => row.1 != id)).push
    (id,{weakMemory := none})).find? (fun row => row.1 == id) = some (id,{weakMemory := none})
  have missing : (state.machine.user.payload.payload.user.runtime.extras.allocations.filter (fun row => row.1 != id)).find?
      (fun row => row.1 == id) = none := by
    apply Array.find?_eq_none.mpr
    intro row member
    have different : row.1 ≠ id := by simpa only [bne_iff_ne] using (Array.mem_filter.mp member).2
    simpa only [beq_iff_eq] using different
  simp [Array.find?_push,missing]
end EmptyFunction.ProjectedWriteContext
