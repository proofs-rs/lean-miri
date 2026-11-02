import duplicate_prefix.GeneralBorrowForestGeneratedTagHistoryConstruct
namespace DuplicatePrefix.GeneralBorrowForestGeneratedTagHistoryStep
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowForestTagHighWater
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem remove_bound (protections : ProtectedTags) (tag counter : BorTag)
    (bound : ∀row∈protections.entries,row.1.value.toNat<counter.value.toNat) :
    ∀row∈(protections.remove tag).entries,row.1.value.toNat<counter.value.toNat := by
  intro row member
  exact bound row (Array.mem_filter.mp member).1

private theorem fold_bound (records : List (AllocId × BorTag)) (counter : BorTag) (protections : ProtectedTags)
    (bound : ∀row∈protections.entries,row.1.value.toNat<counter.value.toNat) :
    ∀row∈(records.foldl (fun tags pair => tags.remove pair.2) protections).entries,row.1.value.toNat<counter.value.toNat := by
  induction records generalizing protections with
  | nil => exact bound
  | cons pair rest ih => exact ih _ (remove_bound protections pair.2 counter bound)

/-- Source endCall only removes stored protector keys, so it cannot raise the
original tag high-water bound. No release-success certificate is assumed. -/
theorem end_call (tree : BorrowTree) (global : GlobalState) (frame : FrameState)
    (below : Below tree global.protectedTags global.nextPointerTag) :
    Below tree (global.endCall frame).protectedTags (global.endCall frame).nextPointerTag := by
  refine ⟨below.mapping,?_⟩
  change ∀row∈(frame.protectedTags.foldl (fun tags pair => tags.remove pair.2) global.protectedTags).entries,
    row.1.value.toNat<global.nextPointerTag.value.toNat
  rw [←Array.foldl_toList]
  exact fold_bound frame.protectedTags.toList global.nextPointerTag global.protectedTags below.protectors

/-- Each actual reached source step preserves structure and high-water data.
The source status is retained: access/release failures stop the history and
are never asserted successful by this data-invariant theorem. Fresh allocation
and mixed constructors derive their successful effects from raw guards. -/
theorem preserves (id : AllocId) (state : Snapshot) (initial : Invariant state) (event : Event)
    (allowed : Applicable state event) :
    Invariant (step id state event).state ∧ (step id state event).state.tree.locations.size=state.tree.locations.size := by
  cases event with
  | allocate =>
    let allocated : GlobalState := {state.global with nextPointerTag:=TypedRetagEmpty.successorTag state.global.nextPointerTag allowed}
    have actual : state.global.newPointerTag=.ok (allocated,state.global.nextPointerTag) := TypedRetagEmpty.allocate_tag state.global allowed
    have full := GenericTagHighWaterPreservation.register_below state.tree state.global.protectedTags state.global.nextPointerTag allowed
      (GeneralBorrowForestTagHighWater.complete _ _ _ initial.below initial.structural.allocator.nodeTags) false
    have nextBelow : Below state.tree allocated.protectedTags allocated.nextPointerTag := ⟨full.mapping,full.protectors⟩
    simp only [step,actual]
    exact ⟨⟨initial.structural,nextBelow⟩,True.intro⟩
  | constructor parent base inside outside held =>
    have checked := GeneralBorrowForestGeneratedTagHistoryConstruct.constructor id state initial parent base inside outside held allowed
    exact ⟨checked.2.1,checked.2.2⟩
  | access source offset len kind mode =>
    have structural := GeneralBorrowStructuralHistoryFrames.access state.tree initial.structural source offset len kind state.global.protectedTags mode allowed
    have frame := GeneralBorrowFreshReadFrame.frame state.tree source offset len kind state.global.protectedTags mode
    have afterBelow : Below (state.tree.performBorrowAccessRange source offset len kind state.global.protectedTags mode).tree state.global.protectedTags state.global.nextPointerTag := by
      rw [frame]
      exact GeneralBorrowForestTagHighWaterHistory.locations _ _ _ _ initial.below
    exact ⟨⟨structural.1,afterBelow⟩,structural.2⟩
  | gc live =>
    have structural := GeneralBorrowStructuralHistoryState.gc state.tree initial.structural live
    have afterBelow := GeneralBorrowForestTagHighWaterHistory.collect state.tree live state.global.protectedTags state.global.nextPointerTag
      initial.below initial.structural.allocator.nodeTags
    exact ⟨⟨structural.2.1,afterBelow⟩,structural.2.2⟩
  | release =>
    cases found : state.frames.back? with
    | none => simp only [Applicable,found,Option.isSome_none,Bool.false_eq_true] at allowed
    | some record =>
      rcases record with ⟨tag,frame⟩
      let actual := state.tree.releaseProtector tag state.global.protectedTags
      have structural := GeneralBorrowStructuralHistoryFrames.release state.tree initial.structural tag state.global.protectedTags
      have treeFrame := GeneralBorrowStructuralReleaseGeometryFrame.release state.tree state.global.protectedTags tag
      have afterBelow : Below actual.tree state.global.protectedTags state.global.nextPointerTag := by
        change actual.tree={state.tree with locations:=actual.tree.locations} at treeFrame
        rw [treeFrame]
        exact GeneralBorrowForestTagHighWaterHistory.locations _ _ _ _ initial.below
      cases released : (state.tree.releaseProtector tag state.global.protectedTags).status==.Released
      · have next : Invariant {state with tree:=actual.tree} := ⟨structural.1,afterBelow⟩
        simpa only [step,found,released,Bool.false_eq_true,↓reduceIte] using And.intro next structural.2
      · have next : Invariant ⟨actual.tree,state.global.endCall frame,state.frames.pop⟩ :=
          ⟨structural.1,end_call actual.tree state.global frame afterBelow⟩
        simpa only [step,found,released,↓reduceIte] using And.intro next structural.2
end DuplicatePrefix.GeneralBorrowForestGeneratedTagHistoryStep
