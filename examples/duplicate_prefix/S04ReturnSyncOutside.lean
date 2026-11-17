import duplicate_prefix.S04ReturnExtrasAccess
import duplicate_prefix.S04SyncSortPreserves

namespace DuplicatePrefix.S04ReturnSyncOutside
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem list_skip {α β E S : Type} (rows : List α) (seed : β)
    (f : α → β → EStateM E S (ForInStep β))
    (step : ∀ row ∈ rows, f row seed = pure (.yield seed)) :
    forIn rows seed f = pure seed := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    rw [List.forIn_cons,step head (by simp)]
    funext state
    simpa only [bind,EStateM.bind,pure,EStateM.pure] using
      congrFun (ih (fun row member => step row (by simp [member]))) state

/-- Raw synchronization entries outside the actual byte range are untouched.
Their payloads and callbacks are unrestricted. Sorting, callback selection and
the deferred-deletion loop are the production operations, not substitutes. -/
theorem sync_access_outside {K U Payload : Type}
    (extras : MemoryExtras.Hooks K U Payload) (machine : MachineHooks.MachineState K U)
    (id : AllocId) (range : AllocRange) (write : Bool)
    (extra : MemoryExtras.AllocationExtra Payload)
    (present : (extras.get machine.user).allocations.find? (fun row => row.1 == id) = some (id,extra))
    (outside : ∀ row ∈ extra.sync,
      row.1.bytes.toNat < range.start.bytes.toNat ∨
      range.start.bytes.toNat+range.size.bytes.toNat ≤ row.1.bytes.toNat) :
    MemoryExtras.syncAccess extras write id range machine = .ok () machine := by
  let objects : Array (Size × SyncObject.Object (MemoryExtras.Machine K U) Payload) :=
    extra.sync.map fun row => (row.1,{payload := row.2.payload, deleteOnWrite := row.2.deleteOnWrite, onAccess := extras.onAccess row.2.payload})
  have outsideObjects : ∀ row ∈ objects,
      row.1.bytes.toNat < range.start.bytes.toNat ∨
      range.start.bytes.toNat+range.size.bytes.toNat ≤ row.1.bytes.toNat := by
    intro row member
    obtain ⟨old,oldMem,equal⟩ := Array.mem_map.mp member
    subst row
    exact outside old oldMem
  have sorted := S04SyncSortPreserves.qsort_all
    (fun row : Size × SyncObject.Object (MemoryExtras.Machine K U) Payload =>
      row.1.bytes.toNat < range.start.bytes.toNat ∨
      range.start.bytes.toNat+range.size.bytes.toNat ≤ row.1.bytes.toNat)
    objects (fun left right => left.1.bytes < right.1.bytes) outsideObjects
  unfold MemoryExtras.syncAccess SyncObject.onMemoryAccess MemoryExtras.accessHooks MemoryExtras.lookup
  unfold_internal ".MemoryExtras.liftResult"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,present]
  change (do
    let deletions ← forIn (objects.qsort (fun left right => left.1.bytes < right.1.bytes)) #[]
      (fun (row : Size × SyncObject.Object (MemoryExtras.Machine K U) Payload) (deletions : Array Size) => do
        let mut deletions := deletions
        if (if write then SyncObject.AccessKind.write else .read) == SyncObject.AccessKind.deallocation ||
            (range.start.bytes.toNat <= row.1.bytes.toNat &&
             row.1.bytes.toNat < range.start.bytes.toNat+range.size.bytes.toNat) then
          row.2.onAccess (if write then .write else .read)
          if (if write then SyncObject.AccessKind.write else .read) == SyncObject.AccessKind.write && row.2.deleteOnWrite then
            deletions := deletions.push row.1
        pure (.yield deletions))
    for offset in deletions do (MemoryExtras.accessHooks extras).remove id offset) machine = _
  rw [←Array.forIn_toList]
  have skipped := list_skip
    (objects.qsort (fun left right => left.1.bytes < right.1.bytes)).toList (#[] : Array Size)
    (fun (row : Size × SyncObject.Object (MemoryExtras.Machine K U) Payload) (deletions : Array Size) => do
      let mut deletions := deletions
      if (if write then SyncObject.AccessKind.write else .read) == SyncObject.AccessKind.deallocation ||
          (range.start.bytes.toNat <= row.1.bytes.toNat &&
           row.1.bytes.toNat < range.start.bytes.toNat+range.size.bytes.toNat) then
        row.2.onAccess (if write then .write else .read)
        if (if write then SyncObject.AccessKind.write else .read) == SyncObject.AccessKind.write && row.2.deleteOnWrite then
          deletions := deletions.push row.1
      pure (.yield deletions)) (by
        intro row member
        have separation := sorted row (Array.mem_toList_iff.mp member)
        have noHit : ¬(range.start.bytes.toNat ≤ row.1.bytes.toNat ∧
          row.1.bytes.toNat < range.start.bytes.toNat+range.size.bytes.toNat) := by omega
        cases write <;> simp [noHit])
  rw [skipped]
  rfl

end DuplicatePrefix.S04ReturnSyncOutside
