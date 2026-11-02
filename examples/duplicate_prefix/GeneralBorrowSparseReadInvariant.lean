import duplicate_prefix.GeneralBorrowProtectedReadInvariant
namespace DuplicatePrefix.GeneralBorrowSparseReadInvariant
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowStorage
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Compatibility with a Read through any tag in the same tree. Active held
Default reservations are admitted; active held Unique and ReservedIM are not. -/
abbrev Readable := GeneralBorrowProtectedReadInvariant.Readable

def Data (mask : Nat → Prop) (tree : NormalTreeState) : Prop :=
  ∀ index,mask index → index < tree.locationStates.size → ∃ state,tree.stateAt index = some state ∧
    Readable state (tree.protectedNodes.contains index)

private theorem access (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : Readable state held) : ∃ next transition,
    state.performAccess .Read related held = .Success next transition ∧ Readable next held := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Readable,GeneralBorrowProtectedReadInvariant.Readable,LocationState.possible,Permission.isUnique] at initial <;>
      (refine ⟨_,_,rfl,?_⟩;simp [Readable,GeneralBorrowProtectedReadInvariant.Readable,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign])
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Readable,GeneralBorrowProtectedReadInvariant.Readable,LocationState.possible,Permission.isUnique] at initial <;>
      (refine ⟨_,_,rfl,?_⟩;simp [Readable,GeneralBorrowProtectedReadInvariant.Readable,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign])

private theorem record (state recorded : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : Readable state held) (actual : state.recordNewAccess .Read related = .Recorded recorded) :
    Readable recorded held := by
  unfold LocationState.recordNewAccess at actual
  split at actual
  · cases actual;exact initial
  · cases actual

private theorem update (mask : Nat → Prop) (tree : NormalTreeState) (initial : Data mask tree) (index : Nat)
    (valid : index < tree.locationStates.size) (next : LocationState)
    (readable : Readable next (tree.protectedNodes.contains index)) :
    Data mask {tree with locationStates := tree.locationStates.set index (some next) valid} := by
  intro query selected bounded
  have oldBound : query < tree.locationStates.size := by simpa only [Array.size_set] using bounded
  by_cases same : query = index
  · subst query
    exact ⟨next,by simp [NormalTreeState.stateAt],readable⟩
  · obtain ⟨state,present,good⟩ := initial query selected oldBound
    exact ⟨state,(stateAt_update_other tree index query next valid same).trans present,good⟩

/-- The real source event processor preserves Read compatibility at every tag,
including early debug-record exits. No successful access is a hypothesis. -/
theorem events (mask : Nat → Prop) (items : List TraversalEvent) (root : Nat) (tree : NormalTreeState)
    (selected : ∀ event ∈ items,mask event.node) (initial : Data mask tree) :
    Data mask (sourceNormalEvents tree root .Read items).tree := by
  induction items generalizing tree with
  | nil => unfold_normal_events;exact initial
  | cons event rest ih =>
    cases present : tree.stateAt event.node with
    | none => unfold_normal_events;simp only [present];exact initial
    | some state =>
      cases recorded : state.recordNewAccess .Read event.relatedness with
      | DebugAssertion => unfold_normal_events;simp only [present,recorded];exact initial
      | Recorded changed =>
        by_cases valid : event.node < tree.locationStates.size
        · obtain ⟨old,oldPresent,good⟩ := initial event.node (selected event (by simp)) valid
          have same : old = state := Option.some.inj (oldPresent.symm.trans present)
          subst old
          have changedGood := record state changed event.relatedness _ good recorded
          obtain ⟨next,transition,performed,nextGood⟩ := access changed event.relatedness _ changedGood
          unfold_normal_events
          simp only [present,recorded,performed,valid,↓reduceDIte]
          exact ih _ (fun later member => selected later (by simp [member])) (update mask tree initial event.node valid next nextGood)
        · unfold_normal_events
          simp only [present,recorded,valid,↓reduceDIte]
          exact initial

end DuplicatePrefix.GeneralBorrowSparseReadInvariant
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowSparseReadInvariant." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved sparse Read invariant dependency {dependency}"
