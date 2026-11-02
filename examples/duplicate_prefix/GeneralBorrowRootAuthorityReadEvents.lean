import duplicate_prefix.GeneralBorrowStructuralHistoryRootAuthorityAt
import duplicate_prefix.GeneralBorrowPhysicalReadable
namespace DuplicatePrefix.GeneralBorrowRootAuthorityReadEvents
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowEvents GeneralBorrowPermissions
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def RootOwned (tree : NormalTreeState) (root : Nat) : Prop :=
  ∀state,tree.stateAt root=some state→LocalOwned state false

private theorem recorded (state changed : LocationState) (owned : LocalOwned state false)
    (actual : state.recordNewAccess .Read .LocalAccess=.Recorded changed) : LocalOwned changed false := by
  unfold LocationState.recordNewAccess at actual
  split at actual
  · cases actual;exact owned
  · cases actual

/-- Even the actual error poststate of a local Read retains latent local
Write permission. Completion is derived separately from raw readability. -/
theorem local_read (state : LocationState) (held : Bool) (owned : LocalOwned state false) :
    LocalOwned (state.performAccess .Read .LocalAccess held).resultingState false := by
  rcases state with ⟨permission,accessed,sifa⟩
  cases permission with
  | ReservedFrz conflicted =>
    cases conflicted <;> cases accessed <;> cases sifa <;> cases held <;>
      simp [LocalOwned,LocationState.possible,Permission.isUnique] at owned <;> (exact ⟨rfl,by trivial⟩)
  | Cell | ReservedIM | Unique | Frozen | Disabled =>
    cases accessed <;> cases sifa <;> cases held <;>
      simp [LocalOwned,LocationState.possible,Permission.isUnique] at owned <;> (exact ⟨rfl,by trivial⟩)

/-- All actual source callback outcomes retain the owning root. Only callbacks
at that root must be local; foreign target states and protector bits are unrestricted. -/
theorem events (items : List TraversalEvent) (resultRoot root : Nat) (tree : NormalTreeState)
    (localRoot : ∀event∈items,event.node=root→event.relatedness=.LocalAccess) (initial : RootOwned tree root) :
    RootOwned (sourceNormalEvents tree resultRoot .Read items).tree root := by
  induction items generalizing tree with
  | nil => unfold_normal_events;exact initial
  | cons event rest ih =>
    cases present : tree.stateAt event.node with
    | none => unfold_normal_events;simp only[present];exact initial
    | some state =>
      cases record : state.recordNewAccess .Read event.relatedness with
      | DebugAssertion => unfold_normal_events;simp only[present,record];exact initial
      | Recorded changed =>
        by_cases valid : event.node<tree.locationStates.size
        · let next := (changed.performAccess .Read event.relatedness (tree.protectedNodes.contains event.node)).resultingState
          let updated := {tree with locationStates:=tree.locationStates.set event.node (some next) valid}
          have nextOwned : RootOwned updated root := by
            intro value found
            by_cases same : root=event.node
            · have related := localRoot event (by simp) same.symm
              have before := initial state (by simpa only[same] using present)
              have changeOwned : LocalOwned changed false := recorded state changed before (by simpa only[related] using record)
              have stored : updated.stateAt root=some next := by simp only[updated,same,NormalTreeState.stateAt,Array.getElem?_set_self]
              have equal : value=next := Option.some.inj (found.symm.trans stored)
              subst value
              dsimp only[next]
              rw[related]
              exact local_read changed _ changeOwned
            · have before := (stateAt_update_other tree event.node root next valid same).symm.trans found
              exact initial value before
          have tailLocal : ∀later∈rest,later.node=root→later.relatedness=.LocalAccess := fun later member=>localRoot later (by simp[member])
          cases performed : changed.performAccess .Read event.relatedness (tree.protectedNodes.contains event.node) with
          | Success value transition =>
            unfold_normal_events
            simp only[present,record,performed,LocationState.AccessResult.resultingState,valid,↓reduceDIte]
            exact ih _ tailLocal (by simpa only[updated,next,performed,LocationState.AccessResult.resultingState] using nextOwned)
          | Error value error | PermissionInvariantFailure value | TransitionApplicationInvariantFailure value | PossibleInvariantFailure value =>
            unfold_normal_events
            simp only[present,record,performed,LocationState.AccessResult.resultingState,valid,↓reduceDIte]
            simpa only[updated,next,performed,LocationState.AccessResult.resultingState] using nextOwned
        · unfold_normal_events
          simp only[present,record,valid,↓reduceDIte]
          exact initial
end DuplicatePrefix.GeneralBorrowRootAuthorityReadEvents
