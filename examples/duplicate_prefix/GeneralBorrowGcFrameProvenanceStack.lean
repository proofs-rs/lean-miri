import duplicate_prefix.GeneralBorrowGcFrameProvenanceVisitor
namespace DuplicatePrefix.GeneralBorrowGcFrameProvenanceStack
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows ProvenanceGC
open GeneralBorrowGcFrameProvenanceScalar GeneralBorrowGcFrameProvenanceFold GeneralBorrowGcFrameProvenanceVisitor
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def Carries (id : AllocId) (tag : BorTag) (frame : ActualFrame) : Prop :=
  (∃ entry ∈ frame.locals, LocalCarries id tag entry) ∨
  ∃ borrow, frame.extra.borrowTracker = some borrow ∧ (id,tag) ∈ borrow.protectedTags

def StackForm (stack : ThreadStacks.ActualStack) : Prop := ∀ frame ∈ stack.frames, FrameForm frame

/-- The real active-stack fold completes from raw frame representation data,
collecting allocation IDs and tags from live locals and frame-owned protectors. -/
theorem stack (roots : Roots) (stack : ThreadStacks.ActualStack) (raw : StackForm stack) :
    ∃ after, roots.stack stack = .ok after ∧ Extends roots after ∧
      ∀ id tag, (∃ frame ∈ stack.frames, Carries id tag frame) → tag ∈ after.tags ∧ id ∈ after.allocations := by
  obtain ⟨after,done,extension,listed⟩ := collect stack.frames.toList Roots.frame Carries
    (fun frame member roots => GeneralBorrowGcFrameProvenanceVisitor.frame roots frame (raw frame (Array.mem_toList_iff.mp member))) roots
  refine ⟨after,?_,extension,?_⟩
  · unfold Roots.stack
    simp only [←Array.forIn_toList]
    have loop : forIn (m := Except StepError) stack.frames.toList roots
        (fun frame current => do return .yield (←current.frame frame)) = .ok after := by
      unfold scan at done
      exact done
    rw [loop]
    rfl
  · intro id tag carried
    rcases carried with ⟨frame,member,pointer⟩
    exact listed id tag ⟨frame,Array.mem_toList_iff.mpr member,pointer⟩

theorem member_of_lookup (values : Array α) (index : Nat) (value : α)
    (present : values[index]? = some value) : value ∈ values := by
  have valid : index < values.size := by
    by_cases valid : index < values.size
    · exact valid
    · rw [Array.getElem?_eq_none (by omega)] at present
      cases present
  have same := Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans present)
  rw [←same]
  exact Array.getElem_mem valid

/-- Thin or wide scalar provenance in an actual indexed live stack local is
collected directly by the source visitor; the pointer is never dereferenced. -/
theorem local_pointer (roots : Roots) (stack : ThreadStacks.ActualStack) (raw : StackForm stack)
    (frameIndex localId : Nat) (frame : ActualFrame) (entry : LocalState Provenance LocalLayout)
    (framePresent : stack.frames[frameIndex]? = some frame)
    (localPresent : frame.locals[localId]? = some entry)
    (id : AllocId) (tag : BorTag) (value : Immediate Provenance)
    (live : entry.value = .live (.immediate value))
    (pointer : GeneralBorrowGcFrameProvenanceScalar.Carries id tag value) :
    ∃ after, roots.stack stack = .ok after ∧ Extends roots after ∧ after.tags.contains tag = true ∧ after.allocations.contains id = true := by
  obtain ⟨after,done,extension,listed⟩ := GeneralBorrowGcFrameProvenanceStack.stack roots stack raw
  have found := listed id tag ⟨frame,member_of_lookup stack.frames frameIndex frame framePresent,
    Or.inl ⟨entry,member_of_lookup frame.locals localId entry localPresent,value,live,pointer⟩⟩
  exact ⟨after,done,extension,Array.contains_iff_mem.mpr found.1,Array.contains_iff_mem.mpr found.2⟩

/-- The source visitor traces frame-owned `(allocation,tag)` protectors after
locals. Global protector membership is unnecessary for this collection fact. -/
theorem protector (roots : Roots) (stack : ThreadStacks.ActualStack) (raw : StackForm stack)
    (frameIndex : Nat) (frame : ActualFrame) (borrow : FrameState) (id : AllocId) (tag : BorTag)
    (framePresent : stack.frames[frameIndex]? = some frame)
    (borrowPresent : frame.extra.borrowTracker = some borrow)
    (stored : (id,tag) ∈ borrow.protectedTags) :
    ∃ after, roots.stack stack = .ok after ∧ Extends roots after ∧ after.tags.contains tag = true ∧ after.allocations.contains id = true := by
  obtain ⟨after,done,extension,listed⟩ := GeneralBorrowGcFrameProvenanceStack.stack roots stack raw
  have found := listed id tag ⟨frame,member_of_lookup stack.frames frameIndex frame framePresent,
    Or.inr ⟨borrow,borrowPresent,stored⟩⟩
  exact ⟨after,done,extension,Array.contains_iff_mem.mpr found.1,Array.contains_iff_mem.mpr found.2⟩

end DuplicatePrefix.GeneralBorrowGcFrameProvenanceStack
