import duplicate_prefix.GeneralBorrowGcFrameProvenanceUserVisits
namespace DuplicatePrefix.GeneralBorrowGcFrameProvenanceMachineRoots
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Concurrency ProvenanceGC
open GeneralBorrowGcFrameProvenanceScalar GeneralBorrowGcFrameProvenanceMonotone
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

theorem entry (roots : Roots) (pointers : MachineGCRoots.EntryPointers) (statics : ExternStatic.State) :
    Result roots (do
      let mut current := roots
      if let some place := pointers.mainReturn then current ← current.memPlace place.mplace
      for pointer in #[pointers.argc,pointers.argv,pointers.commandLine] do
        if let some pointer := pointer then current := current.strictPointer pointer
      return current.externStatics statics) := by
  let finish (initial : Roots) : Except StepError Roots := do
    let mut current := initial
    for pointer in #[pointers.argc,pointers.argv,pointers.commandLine] do
      if let some pointer := pointer then current := current.strictPointer pointer
    return current.externStatics statics
  have complete : ∀ initial, Result initial (finish initial) := by
    intro initial
    dsimp only [finish]
    apply chain initial _ _
    · rw [←Array.forIn_toList]
      apply loop
      intro optional member before out success
      cases optional with
      | none =>
        simp only [pure,Except.pure] at success
        cases success
        exact extends_refl before
      | some pointer =>
        simp only [pure,Except.pure] at success
        cases success
        exact provenance_extends before pointer.provenance
    · intro after
      intro final success
      cases success
      exact GeneralBorrowGcFrameProvenanceUserVisits.externStatics after statics
  cases pointers.mainReturn with
  | none => exact complete roots
  | some place => exact chain roots _ _ (memPlace roots place.mplace) complete

/-- The actual complete user-root visitor retains every already collected
allocation/tag on its successful branch. Token-validation and representation
errors remain explicit outcomes, rather than premises declaring success. -/
theorem visit (views : MachineGCRoots.Views User Os R Payload H D O)
    (state : MachineHooks.State K User) (roots : Roots) :
    Result roots (MachineGCRoots.visit views state roots) := by
  unfold MachineGCRoots.visit
  apply chain roots _ _ (GeneralBorrowGcFrameProvenanceUserVisits.unwindPayloads roots state.machine.threads (views.unwindPayloads state.machine.user))
  intro a
  apply chain a _ _ (GeneralBorrowGcFrameProvenanceUserVisits.errno a state.machine.threads (views.errnoPlaces state.machine.user))
  intro b
  apply chain b _ _ (GeneralBorrowGcFrameProvenanceUserVisits.inactiveStacks b state.machine.threads (views.stacks state.machine.user))
  intro c
  apply chain c _ _ (GeneralBorrowGcFrameProvenanceUserVisits.threadLocal c state.machine.threads (views.tls state.machine.user).statics)
  intro d
  apply chain d _ _ (GeneralBorrowGcFrameProvenanceUserVisits.threadTls d (views.tls state.machine.user).values)
  intro e
  apply of_extension e (MachineGCRoots.visitDirectories (e.envVars (views.environment state.machine.user)) (views.directories state.machine.user)) _
    (extends_trans (GeneralBorrowGcFrameProvenanceUserVisits.envVars e (views.environment state.machine.user))
      (GeneralBorrowGcFrameProvenanceUserVisits.directories _ (views.directories state.machine.user)))
  apply chain _ _ _ (GeneralBorrowGcFrameProvenanceUserVisits.weakMemory _ _)
  intro afterWeak
  exact entry afterWeak (views.entry state.machine.user) (views.externStatics state.machine.user)


/-- The real source rootset after allocation, active-stack and full user
visitation contains the provenance of the indexed actual local. The two
outcome equations are intermediate branch eliminators, not assumed GC success
in the eventual whole-machine retention contract. -/
theorem local_rootsHeld (views : MachineGCRoots.Views User Os R Payload H D O)
    (state : MachineHooks.State K User)
    (raw : GeneralBorrowGcFrameProvenanceStack.StackForm state.stack)
    (frameIndex localId : Nat) (frame : GeneralBorrowGcFrameProvenanceVisitor.ActualFrame)
    (entry : LocalState Provenance LocalLayout)
    (framePresent : state.stack.frames[frameIndex]? = some frame)
    (localPresent : frame.locals[localId]? = some entry)
    (id : AllocId) (tag : BorTag) (value : Immediate Provenance)
    (live : entry.value = .live (.immediate value))
    (pointer : GeneralBorrowGcFrameProvenanceScalar.Carries id tag value) :
    ∀ collected after, GeneralBorrowGcFrameProvenanceCollection.collect state = .ok collected →
      MachineGCRoots.visit views state collected = .ok after →
      after.tags.contains tag = true ∧ after.allocations.contains id = true := by
  obtain ⟨known,done,_,tagHeld,idHeld⟩ := GeneralBorrowGcFrameProvenanceStack.local_pointer
    (GeneralBorrowGcFrameProvenanceCollection.allocationRoots state) state.stack raw
    frameIndex localId frame entry framePresent localPresent id tag value live pointer
  intro collected after actual success
  have same : known = collected := Except.ok.inj (done.symm.trans actual)
  subst known
  have extension := visit views state collected after success
  exact ⟨Array.contains_iff_mem.mpr (extension.1 tag (Array.contains_iff_mem.mp tagHeld)),
    Array.contains_iff_mem.mpr (extension.2 id (Array.contains_iff_mem.mp idHeld))⟩

/-- Actual frame-owned protected tags reach the same complete source rootset. -/
theorem protector_rootsHeld (views : MachineGCRoots.Views User Os R Payload H D O)
    (state : MachineHooks.State K User)
    (raw : GeneralBorrowGcFrameProvenanceStack.StackForm state.stack)
    (frameIndex : Nat) (frame : GeneralBorrowGcFrameProvenanceVisitor.ActualFrame) (borrow : FrameState)
    (framePresent : state.stack.frames[frameIndex]? = some frame)
    (borrowPresent : frame.extra.borrowTracker = some borrow)
    (id : AllocId) (tag : BorTag) (stored : (id,tag) ∈ borrow.protectedTags) :
    ∀ collected after, GeneralBorrowGcFrameProvenanceCollection.collect state = .ok collected →
      MachineGCRoots.visit views state collected = .ok after →
      after.tags.contains tag = true ∧ after.allocations.contains id = true := by
  obtain ⟨known,done,_,tagHeld,idHeld⟩ := GeneralBorrowGcFrameProvenanceStack.protector
    (GeneralBorrowGcFrameProvenanceCollection.allocationRoots state) state.stack raw
    frameIndex frame borrow id tag framePresent borrowPresent stored
  intro collected after actual success
  have same : known = collected := Except.ok.inj (done.symm.trans actual)
  subst known
  have extension := visit views state collected after success
  exact ⟨Array.contains_iff_mem.mpr (extension.1 tag (Array.contains_iff_mem.mp tagHeld)),
    Array.contains_iff_mem.mpr (extension.2 id (Array.contains_iff_mem.mp idHeld))⟩

end DuplicatePrefix.GeneralBorrowGcFrameProvenanceMachineRoots
