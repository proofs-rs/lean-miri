import duplicate_prefix.GeneralBorrowProtectedReadInvariant
import duplicate_prefix.GeneralBorrowNormalSifaConsistency
import duplicate_prefix.GeneralBorrowExposedNonleafRead
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationReadSifa
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowEvents GeneralBorrowStorage GeneralBorrowFreshActiveOnClean
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem recorded_readable (state changed : LocationState) (related : AccessRelatedness) (held : Bool)
    (good : GeneralBorrowProtectedReadInvariant.Readable state held)
    (recorded : state.recordNewAccess .Read related = .Recorded changed) :
    GeneralBorrowProtectedReadInvariant.Readable changed held := by
  unfold LocationState.recordNewAccess at recorded
  split at recorded
  · cases recorded;exact good
  · cases recorded

/-- Actual scheduled source Read processing preserves physical scalar SIFA
bounds with several simultaneously held active reservations. Strong exclusive
foreign ownership is not required. Completion is established independently. -/
theorem events (items : List TraversalEvent) (root : Nat) (tree : NormalTreeState)
    (readable : GeneralBorrowProtectedReadInvariant.Data tree)
    (physical : GeneralBorrowNormalSifaConsistency.Profile tree) :
    GeneralBorrowNormalSifaConsistency.Profile (sourceNormalEvents tree root .Read items).tree := by
  induction items generalizing tree with
  | nil => unfold_normal_events;exact physical
  | cons event rest ih =>
    cases present : tree.stateAt event.node with
    | none => unfold_normal_events;simp only [present];exact physical
    | some state =>
      cases recorded : state.recordNewAccess .Read event.relatedness with
      | DebugAssertion => unfold_normal_events;simp only [present,recorded];exact physical
      | Recorded changed =>
        by_cases valid : event.node < tree.locationStates.size
        · obtain ⟨old,oldPresent,good⟩ := readable event.node valid
          have same : old = state := Option.some.inj (oldPresent.symm.trans present)
          subst old
          have changedGood := recorded_readable state changed event.relatedness _ good recorded
          obtain ⟨next,transition,performed,nextGood,support⟩ := GeneralBorrowExposedNonleafRead.transition changed event.relatedness _ changedGood
          have nextPhysical := GeneralBorrowSifaPermissionConsistency.pipeline state changed next transition .Read event.relatedness
            (tree.protectedNodes.contains event.node) (physical event.node state present) recorded performed
          let updated := {tree with locationStates := tree.locationStates.set event.node (some next) valid}
          have updatedReadable : GeneralBorrowProtectedReadInvariant.Data updated := by
            intro query bounded
            have oldBound : query < tree.locationStates.size := by simpa only [updated,Array.size_set] using bounded
            by_cases equal : query = event.node
            · subst query
              exact ⟨next,by simp only [updated,NormalTreeState.stateAt,Array.getElem?_set_self],nextGood⟩
            · obtain ⟨old,found,oldGood⟩ := readable query oldBound
              exact ⟨old,(stateAt_update_other tree event.node query next valid equal).trans found,oldGood⟩
          have updatedPhysical : GeneralBorrowNormalSifaConsistency.Profile updated := by
            intro query value found
            by_cases equal : query = event.node
            · subst query
              have stored : updated.stateAt event.node = some next := by simp only [updated,NormalTreeState.stateAt,Array.getElem?_set_self]
              have same : value = next := Option.some.inj (found.symm.trans stored)
              subst value
              exact nextPhysical
            · exact physical query value ((stateAt_update_other tree event.node query next valid equal).symm.trans found)
          unfold_normal_events
          simp only [present,recorded,performed,valid,↓reduceDIte]
          exact ih updated updatedReadable updatedPhysical
        · unfold_normal_events
          simp only [present,recorded,valid,↓reduceDIte]
          exact physical

theorem normal (tree : NormalTreeState) (forest : GeneralBorrowForest.Forest tree.topology)
    (anchor : Nat) (valid : anchor < tree.topology.nodes.size) (mode : ChildrenVisitMode)
    (aligned : tree.locationStates.size = tree.topology.nodes.size)
    (readable : GeneralBorrowProtectedReadInvariant.Data tree)
    (physical : GeneralBorrowNormalSifaConsistency.Profile tree) :
    (tree.performAccess anchor .Read mode).status = .Completed ∧
      GeneralBorrowNormalSifaConsistency.Profile (tree.performAccess anchor .Read mode).tree := by
  exact ⟨(GeneralBorrowProtectedReadInvariant.normal tree forest anchor valid mode aligned readable).1,
    events _ _ tree readable physical⟩
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationReadSifa
