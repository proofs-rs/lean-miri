import duplicate_prefix.GeneralBorrowGcFrameProvenanceMonotone
namespace DuplicatePrefix.GeneralBorrowGcFrameProvenanceUserVisits
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Concurrency ProvenanceGC
open GeneralBorrowGcFrameProvenanceScalar GeneralBorrowGcFrameProvenanceMonotone
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem inactiveStacks (roots : Roots) (manager : ThreadManager) (registry : ThreadStacks.Registry) :
    Result roots (roots.inactiveStacks manager registry) := by
  unfold Roots.inactiveStacks
  apply GeneralBorrowGcFrameProvenanceMonotone.guard
  intro checked
  apply chain roots _ _
  · rw [←Array.forIn_toList]
    apply loop
    intro saved member before out success
    exact yielding before (before.stack saved.stack) (stack before saved.stack) out success
  · intro after
    exact pure_result after

theorem threadTls (roots : Roots) (data : ThreadTlsData Provenance) : Result roots (roots.threadTls data) := by
  unfold Roots.threadTls
  apply chain roots _ _
  · rw [←Array.forIn_toList]
    apply loop
    intro entry member before out success
    cases entry with
    | pointer pointer =>
      simp only [pure,Except.pure] at success
      cases success
      exact pointer_extends before pointer
    | scalar value => exact yielding before (before.scalar value) (scalar before value) out success
  · intro after
    exact pure_result after

theorem weakMemory (roots : Roots) (registry : MemoryExtras.Registry Payload) : Result roots (roots.weakMemory registry) := by
  unfold Roots.weakMemory
  apply chain roots _ _
  · rw [←Array.forIn_toList]
    apply loop
    intro value member before out success
    exact yielding before (before.scalar value) (scalar before value) out success
  · intro after
    exact pure_result after

theorem envVars (roots : Roots) (env : EnvVars.State (Option Provenance) Os) : Extends roots (roots.envVars env) := by
  unfold Roots.envVars
  rw [←Array.foldl_toList]
  exact fold _ Roots.pointer pointer_extends roots

theorem externStatics (roots : Roots) (state : ExternStatic.State) : Extends roots (roots.externStatics state) := by
  unfold Roots.externStatics
  rw [←Array.foldl_toList]
  exact fold _ Roots.strictPointer (fun before pointer => provenance_extends before pointer.provenance) roots

theorem directories (roots : Roots) (table : UnixDirectories.Table R) : Extends roots (MachineGCRoots.visitDirectories roots table) := by
  unfold MachineGCRoots.visitDirectories
  rw [←Array.foldl_toList]
  apply fold
  intro before entry
  cases entry with
  | mk key stream =>
    dsimp only
    cases stored : stream.entry with
    | none => simpa only [stored] using extends_refl before
    | some pointer =>
      cases pointer with
      | mk pointer rest => simpa only [stored] using pointer_extends before pointer


theorem unwindPayloads (roots : Roots) (manager : ThreadManager) (store : Unwind.PayloadStore) :
    Result roots (roots.unwindPayloads manager store) := by
  unfold Roots.unwindPayloads
  apply chain roots _ _
  · apply loop
    intro thread member before out success
    apply yielding before _ _ out success
    apply loop
    intro token member current result completed
    cases stored : (store.values.filter (·.1 == token))[0]? with
    | none => simp only [stored,throw] at completed; cases completed
    | some entry =>
      simp only [stored] at completed
      split at completed
      · simp only [throw] at completed; cases completed
      · exact yielding current (current.immediate entry.2.imm) (immediate current entry.2.imm) result completed
  · intro after
    exact pure_result after

theorem errno (roots : Roots) (manager : ThreadManager) (storage : Array (AllocId × MPlaceTy Provenance)) :
    Result roots (MachineGCRoots.visitErrno roots manager storage) := by
  unfold MachineGCRoots.visitErrno
  apply chain roots _ _
  · apply loop
    intro thread member before out success
    cases stored : thread.lastErrorLocation with
    | none =>
      simp only [stored,pure,Except.pure] at success
      cases success
      exact extends_refl before
    | some token =>
      simp only [stored] at success
      cases found : (storage.filter (fun entry => entry.1.value.toNat == token))[0]? with
      | none => simp only [found,throw] at success; cases success
      | some entry =>
        cases entry with
        | mk id place =>
          simp only [found] at success
          split at success
          · simp only [throw] at success; cases success
          · exact yielding before (before.memPlace place.mplace) (memPlace before place.mplace) out success
  · intro after
    exact pure_result after

theorem threadLocal (roots : Roots) (manager : ThreadManager) (entries : Array (ThreadLocalEntry Provenance)) :
    Result roots (roots.threadLocalAllocations manager entries) := by
  unfold Roots.threadLocalAllocations
  apply chain roots _ _
  · apply loop
    intro entry member before out success
    cases found : (entries.filter (fun pointer => pointer.runtimeId.value.toNat == entry.pointerToken))[0]? with
    | none => simp only [found,throw] at success; cases success
    | some pointer =>
      simp only [found] at success
      split at success
      · simp only [throw] at success; cases success
      · split at success
        · simp only [throw] at success; cases success
        · simp only [pure,Except.pure] at success
          cases success
          exact provenance_extends before pointer.pointer.provenance
  · intro after
    exact pure_result after

end DuplicatePrefix.GeneralBorrowGcFrameProvenanceUserVisits
