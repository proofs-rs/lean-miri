import duplicate_prefix.GeneralBorrowProtectedReadLocation
namespace DuplicatePrefix.GeneralBorrowProtectedReadInvariant
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowStorage
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Compatibility with a Read through any tag in the same tree. Active held
Default reservations are admitted; active held Unique and ReservedIM are not. -/
def Readable (state : LocationState) (held : Bool) : Prop :=
  state.possible = true ∧ state.permission ≠ .Disabled ∧
    (held = true → state.permission ≠ .Unique ∧ state.permission ≠ .ReservedIM)

def Data (tree : NormalTreeState) : Prop :=
  ∀ index,index < tree.locationStates.size → ∃ state,tree.stateAt index = some state ∧
    Readable state (tree.protectedNodes.contains index)

theorem compatible (state : LocationState) (held : Bool) (related : AccessRelatedness)
    (initial : Readable state held) : GeneralBorrowProtectedReadCompatible.Compatible state related held := by
  cases related
  · exact ⟨initial.1,initial.2.1⟩
  · exact ⟨initial.1,fun held => ⟨(initial.2.2 held).1,(initial.2.2 held).2,fun disabled => False.elim (initial.2.1 disabled)⟩⟩

theorem reservation (conflicted accessed : Bool) (sifa : IdempotentForeignAccess) (held : Bool) :
    Readable ⟨.ReservedFrz conflicted,accessed,sifa⟩ held := by
  cases conflicted <;> cases accessed <;> cases held <;> simp [Readable,LocationState.possible,Permission.isUnique]

private theorem access (state : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : Readable state held) : ∃ next transition,
    state.performAccess .Read related held = .Success next transition ∧ Readable next held := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Readable,LocationState.possible,Permission.isUnique] at initial <;>
      (refine ⟨_,_,rfl,?_⟩;simp [Readable,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign])
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases related <;> cases held <;>
      simp [Readable,LocationState.possible,Permission.isUnique] at initial <;>
      (refine ⟨_,_,rfl,?_⟩;simp [Readable,LocationState.possible,Permission.isUnique,AccessRelatedness.isForeign])

private theorem record (state recorded : LocationState) (related : AccessRelatedness) (held : Bool)
    (initial : Readable state held) (actual : state.recordNewAccess .Read related = .Recorded recorded) :
    Readable recorded held := by
  unfold LocationState.recordNewAccess at actual
  split at actual
  · cases actual;exact initial
  · cases actual

private theorem update (tree : NormalTreeState) (initial : Data tree) (index : Nat)
    (valid : index < tree.locationStates.size) (next : LocationState)
    (readable : Readable next (tree.protectedNodes.contains index)) :
    Data {tree with locationStates := tree.locationStates.set index (some next) valid} := by
  intro query bounded
  have oldBound : query < tree.locationStates.size := by simpa only [Array.size_set] using bounded
  by_cases same : query = index
  · subst query
    exact ⟨next,by simp [NormalTreeState.stateAt],readable⟩
  · obtain ⟨state,present,good⟩ := initial query oldBound
    exact ⟨state,(stateAt_update_other tree index query next valid same).trans present,good⟩

/-- The real source event processor preserves Read compatibility at every tag,
including early debug-record exits. No successful access is a hypothesis. -/
theorem events (items : List TraversalEvent) (root : Nat) (tree : NormalTreeState) (initial : Data tree) :
    Data (sourceNormalEvents tree root .Read items).tree := by
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
        · obtain ⟨old,oldPresent,good⟩ := initial event.node valid
          have same : old = state := Option.some.inj (oldPresent.symm.trans present)
          subst old
          have changedGood := record state changed event.relatedness _ good recorded
          obtain ⟨next,transition,performed,nextGood⟩ := access changed event.relatedness _ changedGood
          unfold_normal_events
          simp only [present,recorded,performed,valid,↓reduceDIte]
          exact ih _ (update tree initial event.node valid next nextGood)
        · unfold_normal_events
          simp only [present,recorded,valid,↓reduceDIte]
          exact initial

/-- Every actual Read, through either visitor mode and any valid anchor,
completes and preserves compatibility for a later Read through any other tag. -/
theorem normal (tree : NormalTreeState) (forest : GeneralBorrowForest.Forest tree.topology)
    (anchor : Nat) (valid : anchor < tree.topology.nodes.size) (mode : ChildrenVisitMode)
    (aligned : tree.locationStates.size = tree.topology.nodes.size) (initial : Data tree) :
    (tree.performAccess anchor .Read mode).status = .Completed ∧ Data (tree.performAccess anchor .Read mode).tree := by
  refine ⟨GeneralBorrowProtectedReadCompatible.normal tree forest anchor valid mode aligned ?_,events _ _ tree initial⟩
  intro index bounded
  obtain ⟨state,present,good⟩ := initial index (by omega)
  exact ⟨state,present,compatible state _ _ good⟩
end DuplicatePrefix.GeneralBorrowProtectedReadInvariant
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadInvariant.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected Read invariant dependency {dependency}"
