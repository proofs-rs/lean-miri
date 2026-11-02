import duplicate_prefix.MemoryCopyBridge

namespace DuplicatePrefix.S04ReturnExtrasAccess
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Synchronization metadata is unrelated to the weak-memory stage. Retain an
arbitrary initial sync registry instead of requiring the entire extras row to
be empty. -/
theorem weak_write_without_buffer {K U Payload : Type}
    (extras : MemoryExtras.Hooks K U Payload) (machine : MachineHooks.MachineState K U)
    (id : AllocId) (range : AllocRange) (sync : Array (Size × MemoryExtras.Entry Payload))
    (present : (extras.get machine.user).allocations.find? (fun row => row.1 == id) =
      some (id, ⟨none,sync⟩)) :
    MemoryExtras.nonAtomicWrite extras id range machine = .ok () machine := by
  unfold MemoryExtras.nonAtomicWrite MemoryExtras.lookup
  unfold_internal ".MemoryExtras.liftResult"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,present]

/-- Exact physical write-access boundary with arbitrary synchronization
metadata. The source diagnostic/race/weak/TB/sync order and every callback
mutation/error are retained. No sync success, empty registry, canonical tree,
allocation size or offset is a premise. This is an operation equation, not
whole-call safety or a claim that Contract currently supplies extras coherence. -/
theorem source_write_access_exact {Os R P H D O Aff B Host : Type}
    (prepared : Miri.Input.CompilerProviders.Prepared)
    (image : Miri.Input.AllocationImage.Imported) (maximum : Size) (fuel : Nat)
    (globals : GlobalAllocationHooks Provenance BorrowTree MiriMemoryKind
      (PlaceMachine.AccessState MiriMemoryKind (Miri.Input.EvalCoreMachine.User Os R P H D O Aff B Host)))
    (pointers : PointerMachine.Hooks MiriMemoryKind
      (ValidityMachine.Control (Miri.Input.EvalCoreMachine.Stored Os R P H D O Aff B Host)))
    (extras : MemoryExtras.Hooks MiriMemoryKind
      (Miri.Input.EvalCoreMachine.User Os R P H D O Aff B Host) P)
    (machine : MachineHooks.MachineState MiriMemoryKind
      (Miri.Input.EvalCoreMachine.User Os R P H D O Aff B Host))
    (tracker : MachineHooks.BorrowState) (tree : BorrowTree)
    (id : AllocId) (provenance : ProvenanceExtra) (range : AllocRange)
    (sync : Array (Size × MemoryExtras.Entry P))
    (noClocks : machine.dataRace = none)
    (noBackend : machine.user.payload.payload.user.backend = .none)
    (tracked : machine.borrowTracker = some tracker)
    (present : (extras.get machine.user).allocations.find? (fun row => row.1 == id) =
      some (id,⟨none,sync⟩)) :
    let config := Miri.Input.EvalAccessMachine.make prepared image maximum fuel globals pointers extras
    let access := tree.performBorrowAccessRange provenance range.start range.size
      .Write tracker.global.protectedTags .VisitChildrenOfAccessed
    PlaceMachine.memoryAccess config true ⟨machine,none⟩ tree id provenance range =
      if access.status = .Completed then
        match MemoryExtras.syncAccess extras true id range machine with
        | .ok _ after => ⟨⟨after,none⟩,access.tree,.ok ()⟩
        | .error error after => ⟨⟨after,some error⟩,access.tree,.error (reprStr error)⟩
      else ⟨⟨machine,some (source_tree_error access.status)⟩,access.tree,
        .error (reprStr (source_tree_error access.status))⟩ := by
  dsimp only
  have diagnostic :
      (Miri.Input.EvalAccessMachine.make prepared image maximum fuel globals pointers extras).diagnostic
        true id range machine = .ok () machine := by
    simp [Miri.Input.EvalAccessMachine.make,
      Miri.Input.EvalBackendMachine.access, Miri.Input.EvalBackendMachine.handler,
      noBackend,noClocks,get,getThe,MonadStateOf.get,EStateM.get,
      bind,EStateM.bind,pure,EStateM.pure,Except.pure,Except.bind]
  have weak :
      (Miri.Input.EvalAccessMachine.make prepared image maximum fuel globals pointers extras).weakMemoryWrite =
        MemoryExtras.nonAtomicWrite extras := rfl
  have syncEq :
      (Miri.Input.EvalAccessMachine.make prepared image maximum fuel globals pointers extras).syncAccess =
        MemoryExtras.syncAccess extras := rfl
  unfold PlaceMachine.memoryAccess
  unfold_internal ".PlaceMachine.bridge"
  simp only [diagnostic,weak,syncEq,pure,Id.run,↓reduceIte]
  rw [MemoryCopyBridge.race_access_without_clocks machine id range (some .Write) .Read noClocks]
  simp only [↓reduceIte]
  rw [weak_write_without_buffer extras machine id range sync present]
  simp only [tracked]
  generalize hAccess : tree.performBorrowAccessRange provenance range.start range.size
    AccessKind.Write tracker.global.protectedTags .VisitChildrenOfAccessed = access
  by_cases completed : access.status = .Completed
  · simp only [completed,↓reduceIte,beq_self_eq_true,Bool.not_true,Bool.false_eq_true]
    cases MemoryExtras.syncAccess extras true id range machine <;> rfl
  · simp [completed]

end DuplicatePrefix.S04ReturnExtrasAccess
