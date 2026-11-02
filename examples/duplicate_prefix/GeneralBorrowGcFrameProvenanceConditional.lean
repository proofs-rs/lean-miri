import duplicate_prefix.GeneralBorrowGcFrameProvenanceMachineRoots
namespace DuplicatePrefix.GeneralBorrowGcFrameProvenanceConditional
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows ProvenanceGC
open GeneralBorrowGcFrameProvenanceScalar GeneralBorrowGcFrameProvenanceMonotone GeneralBorrowGcFrameProvenanceFold
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def Holds (id : AllocId) (tag : BorTag) (roots : Roots) : Prop := tag ∈ roots.tags ∧ id ∈ roots.allocations

theorem extend_holds (before after : Roots) (id : AllocId) (tag : BorTag)
    (held : Holds id tag before) (extension : Extends before after) : Holds id tag after :=
  ⟨extension.1 tag held.1,extension.2 id held.2⟩

/-- Conditional source-fold membership, with no representation or success
assumption about other entries. A failure simply has no completed rootset. -/
theorem loop_member (items : List α) (visit : Roots → α → Except StepError Roots)
    (keeps : ∀ before item, Result before (visit before item))
    (witness : α → Prop) (id : AllocId) (tag : BorTag)
    (collects : ∀ item, witness item → ∀ before after, visit before item = .ok after → Holds id tag after)
    (before after : Roots)
    (done : forIn (m := Except StepError) items before (scan visit) = .ok after)
    (stored : ∃ item ∈ items, witness item) : Holds id tag after := by
  induction items generalizing before with
  | nil => rcases stored with ⟨item,member,_⟩; cases member
  | cons head rest ih =>
    rw [List.forIn_cons] at done
    unfold scan at done
    cases actual : visit before head with
    | error error => simp only [actual,bind,Except.bind] at done; cases done
    | ok middle =>
      simp only [actual,bind,Except.bind,pure,Except.pure] at done
      rcases stored with ⟨item,member,carried⟩
      rcases List.mem_cons.mp member with same | member
      · subst item
        have held := collects head carried before middle actual
        apply extend_holds middle after id tag held
        apply loop rest (scan visit) _ middle after done
        intro item member current out success
        exact yielding current (visit current item) (keeps current item) out success
      · exact ih middle done ⟨item,member,carried⟩


def tail (frame : GeneralBorrowGcFrameProvenanceVisitor.ActualFrame) (initial : Roots) : Except StepError Roots := do
  let mut roots := initial
  if let some caught := frame.extra.catchUnwind then
    roots := roots.pointer caught.catchFn
    roots ← roots.immediate caught.data.imm
    roots ← roots.memPlace caught.dest.mplace
  if let some borrow := frame.extra.borrowTracker then
    for (id,tag) in borrow.protectedTags do roots := roots.add (some id) (some tag)
  return roots

theorem tail_keeps (frame : GeneralBorrowGcFrameProvenanceVisitor.ActualFrame) (roots : Roots) : Result roots (tail frame roots) := by
  unfold tail
  let finish (start : Roots) : Except StepError Roots := do
    let mut current := start
    if let some borrow := frame.extra.borrowTracker then
      for (id,tag) in borrow.protectedTags do current := current.add (some id) (some tag)
    return current
  have finalStep : ∀ start, Result start (finish start) := by
    intro start
    dsimp only [finish]
    cases frame.extra.borrowTracker with
    | none => exact pure_result start
    | some borrow =>
      apply chain start _ _
      · rw [←Array.forIn_toList]
        apply loop
        intro pair member before out success
        cases pair with
        | mk id tag =>
          simp only [pure,Except.pure] at success
          cases success
          exact add_extends before (some id) (some tag)
      · intro after
        exact pure_result after
  cases frame.extra.catchUnwind with
  | none => exact finalStep roots
  | some caught =>
    intro after success
    apply extends_trans (pointer_extends roots caught.catchFn)
    exact chain (roots.pointer caught.catchFn) _ _
      (immediate (roots.pointer caught.catchFn) caught.data.imm)
      (fun middle => chain middle _ _ (memPlace middle caught.dest.mplace) finalStep) after success

theorem frame_eq (roots : Roots) (frame : GeneralBorrowGcFrameProvenanceVisitor.ActualFrame) :
    roots.frame frame = (do
      let first ← roots.runtimePlace frame.returnPlace
      let second ← forIn (m := Except StepError) frame.locals.toList first
        (scan GeneralBorrowGcFrameProvenanceVisitor.localVisit)
      tail frame second) := by
  unfold Roots.frame tail
  simp only [←Array.forIn_toList]
  congr 1
  funext first
  congr 1
  congr 1
  funext entry current
  unfold scan GeneralBorrowGcFrameProvenanceVisitor.localVisit
  cases entry.value <;> rfl


theorem local_keeps (before : Roots) (entry : LocalState Provenance LocalLayout) :
    Result before (GeneralBorrowGcFrameProvenanceVisitor.localVisit before entry) := by
  unfold GeneralBorrowGcFrameProvenanceVisitor.localVisit
  cases entry.value with
  | dead => exact pure_result before
  | live value => exact operand before value

theorem local_collects (id : AllocId) (tag : BorTag) (entry : LocalState Provenance LocalLayout)
    (carried : GeneralBorrowGcFrameProvenanceVisitor.LocalCarries id tag entry)
    (before after : Roots) (done : GeneralBorrowGcFrameProvenanceVisitor.localVisit before entry = .ok after) :
    Holds id tag after := by
  rcases carried with ⟨value,live,pointer⟩
  unfold GeneralBorrowGcFrameProvenanceVisitor.localVisit at done
  rw [live] at done
  obtain ⟨actual,success,_,held,idHeld⟩ := GeneralBorrowGcFrameProvenanceScalar.carries before id tag value pointer
  have same : actual = after := Except.ok.inj (success.symm.trans done)
  subst actual
  exact ⟨held,idHeld⟩

/-- Successful frame collection traces its actual live local regardless of
all other locals' representations and regardless of the catch-unwind fields.
Failure paths need no artificial successful rootset. -/
theorem frame_local (before after : Roots) (frame : GeneralBorrowGcFrameProvenanceVisitor.ActualFrame)
    (id : AllocId) (tag : BorTag)
    (stored : ∃ entry ∈ frame.locals, GeneralBorrowGcFrameProvenanceVisitor.LocalCarries id tag entry)
    (done : before.frame frame = .ok after) : Holds id tag after := by
  rw [frame_eq] at done
  cases place : before.runtimePlace frame.returnPlace with
  | error error => simp only [place,bind,Except.bind] at done; cases done
  | ok first =>
    simp only [place,bind,Except.bind] at done
    cases scanned : forIn (m := Except StepError) frame.locals.toList first
        (scan GeneralBorrowGcFrameProvenanceVisitor.localVisit) with
    | error error => simp only [scanned,bind,Except.bind] at done; cases done
    | ok middle =>
      simp only [scanned,bind,Except.bind] at done
      have held := loop_member frame.locals.toList GeneralBorrowGcFrameProvenanceVisitor.localVisit local_keeps
        (GeneralBorrowGcFrameProvenanceVisitor.LocalCarries id tag) id tag
        (local_collects id tag) first middle scanned (by
          rcases stored with ⟨entry,member,carried⟩
          exact ⟨entry,Array.mem_toList_iff.mpr member,carried⟩)
      exact extend_holds middle after id tag held (tail_keeps frame middle after done)

theorem stack_eq (before : Roots) (stack : ThreadStacks.ActualStack) :
    before.stack stack = (do
      let after ← forIn (m := Except StepError) stack.frames.toList before (scan Roots.frame)
      pure after) := by
  unfold Roots.stack scan
  simp only [←Array.forIn_toList]
  cases forIn (m := Except StepError) stack.frames.toList before
    (fun frame current => do return ForInStep.yield (←current.frame frame)) <;> rfl

/-- A pointer's real active frame/local presence suffices on a completed stack
scan; no global raw-form, missing-catch or collector-success input is needed. -/
theorem stack_local (before after : Roots) (stack : ThreadStacks.ActualStack)
    (id : AllocId) (tag : BorTag)
    (stored : ∃ frame ∈ stack.frames, ∃ entry ∈ frame.locals,
      GeneralBorrowGcFrameProvenanceVisitor.LocalCarries id tag entry)
    (done : before.stack stack = .ok after) : Holds id tag after := by
  rw [stack_eq] at done
  cases scanned : forIn (m := Except StepError) stack.frames.toList before (scan Roots.frame) with
  | error error => simp only [scanned,bind,Except.bind] at done; cases done
  | ok middle =>
    simp only [scanned,bind,Except.bind,pure,Except.pure] at done
    cases done
    apply loop_member stack.frames.toList Roots.frame GeneralBorrowGcFrameProvenanceMonotone.frame
      (fun frame => ∃ entry ∈ frame.locals, GeneralBorrowGcFrameProvenanceVisitor.LocalCarries id tag entry) id tag
    · intro frame carried before after success
      exact frame_local before after frame id tag carried success
    · exact scanned
    · rcases stored with ⟨frame,member,carried⟩
      exact ⟨frame,Array.mem_toList_iff.mpr member,carried⟩


/-- Whole source rootset membership from raw indexed local presence alone.
Other frames, locals, metadata and catch state may cause real collection
errors; no form or success assumption is imposed on those fields. -/
theorem local_rootsHeld (views : MachineGCRoots.Views User Os R Payload H D O)
    (state : MachineHooks.State K User)
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
  intro collected after actual success
  have held := stack_local (GeneralBorrowGcFrameProvenanceCollection.allocationRoots state) collected
    state.stack id tag ⟨frame,GeneralBorrowGcFrameProvenanceStack.member_of_lookup _ _ _ framePresent,
      entry,GeneralBorrowGcFrameProvenanceStack.member_of_lookup _ _ _ localPresent,value,live,pointer⟩ actual
  have retained := extend_holds collected after id tag held
    (GeneralBorrowGcFrameProvenanceMachineRoots.visit views state collected after success)
  exact ⟨Array.contains_iff_mem.mpr retained.1,Array.contains_iff_mem.mpr retained.2⟩

end DuplicatePrefix.GeneralBorrowGcFrameProvenanceConditional
