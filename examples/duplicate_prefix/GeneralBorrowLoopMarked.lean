import duplicate_prefix.GeneralBorrowLoop

namespace DuplicatePrefix.GeneralBorrowLoopMarked
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A finite real forIn list containing a marked assignment ends with a
persistent property established by that assignment. Yield equations and data
invariants are local loop facts; the lemma itself assumes no interpreter safety. -/
theorem eventual {α β : Type} (items : List α) (scan : α → β → Id (ForInStep β))
    (good property : β → Prop) (marked : α → Prop)
    (step : ∀ item ∈ items, ∀ state, good state → ∃ next, scan item state = .yield next ∧ good next)
    (sets : ∀ item ∈ items, marked item → ∀ state, good state → property (scan item state).value)
    (preserves : ∀ item ∈ items, ∀ state, good state → property state → property (scan item state).value)
    (contains : ∃ item ∈ items, marked item) (initial : β) (valid : good initial) :
    good (forIn items initial scan) ∧ property (forIn items initial scan) := by
  induction items generalizing initial with
  | nil => obtain ⟨item,member,_⟩ := contains;cases member
  | cons item rest ih =>
    obtain ⟨next,actual,nextGood⟩ := step item (by simp) initial valid
    have tailStep : ∀ other ∈ rest, ∀ state, good state → ∃ next, scan other state = .yield next ∧ good next :=
      fun other member state stateGood => step other (by simp [member]) state stateGood
    have tailSets : ∀ other ∈ rest, marked other → ∀ state, good state → property (scan other state).value :=
      fun other member marked state stateGood => sets other (by simp [member]) marked state stateGood
    have tailPreserves : ∀ other ∈ rest, ∀ state, good state → property state → property (scan other state).value :=
      fun other member state stateGood stateProperty => preserves other (by simp [member]) state stateGood stateProperty
    rw [List.forIn_cons,actual]
    simp only [bind]
    by_cases selected : marked item
    · have established : property next := by simpa only [actual,ForInStep.value] using sets item (by simp) selected initial valid
      apply GeneralBorrowLoop.list_invariant rest scan (fun state => good state ∧ property state) _ next ⟨nextGood,established⟩
      intro other member state stateGood
      obtain ⟨after,execution,afterGood⟩ := tailStep other member state stateGood.1
      exact ⟨by simpa only [execution,ForInStep.value] using afterGood,
        tailPreserves other member state stateGood.1 stateGood.2⟩
    · apply ih tailStep tailSets tailPreserves _ next nextGood
      obtain ⟨other,member,marked⟩ := contains
      rcases List.mem_cons.mp member with same | member
      · subst other;exact False.elim (selected marked)
      · exact ⟨other,member,marked⟩

end DuplicatePrefix.GeneralBorrowLoopMarked
