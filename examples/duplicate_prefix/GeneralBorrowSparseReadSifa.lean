import duplicate_prefix.GeneralBorrowSparseReadInvariant
import duplicate_prefix.GeneralBorrowNormalSifaConsistency
import duplicate_prefix.GeneralBorrowExposedNonleafRead
namespace DuplicatePrefix.GeneralBorrowSparseReadSifa
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
theorem events (mask : Nat → Prop) (items : List TraversalEvent) (root : Nat) (tree : NormalTreeState)
    (selected : ∀ event ∈ items,mask event.node)
    (readable : GeneralBorrowSparseReadInvariant.Data mask tree)
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
        · obtain ⟨old,oldPresent,good⟩ := readable event.node (selected event (by simp)) valid
          have same : old = state := Option.some.inj (oldPresent.symm.trans present)
          subst old
          have changedGood := recorded_readable state changed event.relatedness _ good recorded
          obtain ⟨next,transition,performed,nextGood,support⟩ := GeneralBorrowExposedNonleafRead.transition changed event.relatedness _ changedGood
          have nextPhysical := GeneralBorrowSifaPermissionConsistency.pipeline state changed next transition .Read event.relatedness
            (tree.protectedNodes.contains event.node) (physical event.node state present) recorded performed
          let updated := {tree with locationStates := tree.locationStates.set event.node (some next) valid}
          have updatedReadable : GeneralBorrowSparseReadInvariant.Data mask updated := by
            intro query selectedQuery bounded
            have oldBound : query < tree.locationStates.size := by simpa only [updated,Array.size_set] using bounded
            by_cases equal : query = event.node
            · subst query
              exact ⟨next,by simp only [updated,NormalTreeState.stateAt,Array.getElem?_set_self],nextGood⟩
            · obtain ⟨old,found,oldGood⟩ := readable query selectedQuery oldBound
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
          exact ih updated (fun later member => selected later (by simp [member])) updatedReadable updatedPhysical
        · unfold_normal_events
          simp only [present,recorded,valid,↓reduceDIte]
          exact physical

end DuplicatePrefix.GeneralBorrowSparseReadSifa
