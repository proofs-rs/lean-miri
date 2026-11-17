import duplicate_prefix.GeneralBorrowGcFrameProvenanceScalar

namespace DuplicatePrefix.GeneralBorrowGcFrameProvenanceFold
open Miri Miri.ABI Miri.Memory Miri.Interpreter ProvenanceGC
open GeneralBorrowGcFrameProvenanceScalar
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def scan (visit : Roots → α → Except StepError Roots) (item : α) (roots : Roots) : Except StepError (ForInStep Roots) := do
  return .yield (←visit roots item)

/-- A source Except-valued visitor loop both completes and collects every
structurally witnessed reference, while retaining its initial collected roots. -/
theorem collect (items : List α) (visit : Roots → α → Except StepError Roots)
    (Carries : AllocId → BorTag → α → Prop)
    (step : ∀ item ∈ items, ∀ roots, ∃ after, visit roots item = .ok after ∧ Extends roots after ∧
      ∀ id tag, Carries id tag item → tag ∈ after.tags ∧ id ∈ after.allocations)
    (roots : Roots) :
    ∃ after, forIn (m := Except StepError) items roots (scan visit) = .ok after ∧ Extends roots after ∧
      ∀ id tag, (∃ item ∈ items, Carries id tag item) → tag ∈ after.tags ∧ id ∈ after.allocations := by
  induction items generalizing roots with
  | nil =>
    refine ⟨roots,rfl,extends_refl roots,?_⟩
    intro id tag member
    rcases member with ⟨item,impossible,_⟩
    cases impossible
  | cons first rest ih =>
    obtain ⟨middle,done,extension,head⟩ := step first (by simp) roots
    obtain ⟨after,tailDone,tailExtension,tail⟩ := ih
      (fun item member => step item (by simp [member])) middle
    refine ⟨after,?_,extends_trans extension tailExtension,?_⟩
    · simp only [List.forIn_cons,scan,done,bind,Except.bind,Except.pure,pure,tailDone]
    · intro id tag member
      rcases member with ⟨item,member,carried⟩
      rcases List.mem_cons.mp member with same | later
      · subst item
        have found := head id tag carried
        exact ⟨tailExtension.1 tag found.1,tailExtension.2 id found.2⟩
      · exact tail id tag ⟨item,later,carried⟩

end DuplicatePrefix.GeneralBorrowGcFrameProvenanceFold
