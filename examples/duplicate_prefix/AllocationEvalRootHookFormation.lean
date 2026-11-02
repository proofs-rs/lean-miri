import duplicate_prefix.AllocationRootHookFormation
import Miri.Input.EvalAllocationMachine
namespace DuplicatePrefix.AllocationEvalRootHookFormation
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter Miri.Input
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem tail
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (extras : MemoryExtras.Hooks MiriMemoryKind (EvalBackendMachine.User Os R P H D O Aff B Host) P)
    (base : PlaceMachine.AllocationConfig MiriMemoryKind (EvalBackendMachine.User Os R P H D O Aff B Host))
    (machine : EvalBackendMachine.Machine Os R P H D O Aff B Host)
    (id : AllocId) (size : Size) (align : Align)
    (noBackend : machine.user.payload.payload.user.backend=.none) (race : machine.dataRace=none) :
    (EvalAllocationMachine.allocation pointers extras base).allocationTail id size align machine=
      MemoryExtras.initAllocation extras id false machine := by
  have selected : EvalBackendMachine.handler machine=.ok .none := by
    simp [EvalBackendMachine.handler,noBackend,race,pure,Pure.pure,Except.pure]
  simp only [EvalAllocationMachine.allocation,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,selected]

/-- The canonical Eval allocation tail selects its real backend-none branch
from initial configuration facts, then installs the actual shared extras. -/
theorem init_extra
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (ThreadStacks.Storage (EvalWorld.World Os R P H D O Aff B Host))))
    (extras : MemoryExtras.Hooks MiriMemoryKind (EvalBackendMachine.User Os R P H D O Aff B Host) P)
    (base : PlaceMachine.AllocationConfig MiriMemoryKind (EvalBackendMachine.User Os R P H D O Aff B Host))
    (before : EvalBackendMachine.Machine Os R P H D O Aff B Host) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (size : Size) (align : Align)
    (enabled : before.borrowTracker=some tracker) (initial : tracker.global=GlobalState.new)
    (race : before.dataRace=none) (noBackend : before.user.payload.payload.user.backend=.none)
    (noExtras : ((extras.get before.user).allocations.any (fun row=>row.1==id))=false) :
    PlaceMachine.initStackExtra (EvalAllocationMachine.allocation pointers extras base).allocationTail id size align before=
      .ok (BorrowTree.new BorTag.one size)
        (MemoryExtras.putAllocation extras (AllocationRootHookFormation.rooted before tracker id) id ⟨none,#[]⟩) := by
  have allocated : tracker.global.rootPointerTag id=.ok (AllocationRootHookFormation.global id,BorTag.one) := by
    rw [initial];exact AllocationRootHookFormation.root id
  have literal := AllocationRootHookFormation.init_extra extras before tracker id size align enabled initial race noExtras
  have actualTail := tail pointers extras base (AllocationRootHookFormation.rooted before tracker id) id size align noBackend race
  dsimp only [AllocationRootHookFormation.rooted] at actualTail
  simp only [race] at actualTail
  simp only [PlaceMachine.initStackExtra,enabled,allocated,race,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure] at literal ⊢
  rw [actualTail]
  exact literal
end DuplicatePrefix.AllocationEvalRootHookFormation
