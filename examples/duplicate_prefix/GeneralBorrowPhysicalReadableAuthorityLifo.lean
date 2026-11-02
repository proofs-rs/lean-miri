import duplicate_prefix.GeneralBorrowRootAuthorityReadableRelease
import duplicate_prefix.GeneralBorrowPhysicalReadableLifo
import duplicate_prefix.GeneralBorrowPhysicalReadableProtections
import duplicate_prefix.GeneralBorrowForestGeneratedTagHistory
namespace DuplicatePrefix.GeneralBorrowPhysicalReadableAuthorityLifo
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralRangeMapState GeneralBorrowStructuralHistoryState
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

open GeneralBorrowPhysicalReadableLifo

private theorem remaining (id : AllocId) (tree : BorrowTree) (global : GlobalState)
    (frames : Array (BorTag × FrameState)) (last : BorTag × FrameState)
    (initial : Frames id tree global (frames.push last)) (next : BorrowTree)
    (same : next={tree with locations:=next.locations}) :
    Frames id next (global.endCall last.2) frames := by
  have nodup := List.nodup_append.mp (by simpa only [Array.toList_push,List.map_append,List.map_singleton] using initial.distinct)
  have singleton := initial.singleton last (by simp)
  refine ⟨fun row member=>initial.singleton row (by simp [member]),nodup.1,?_,?_⟩
  · intro row member
    have different : row.1≠last.1 := by
      intro equal
      exact nodup.2.2 row.1 (List.mem_map.mpr ⟨row,member,rfl⟩) last.1 (by simp) equal
    have before := initial.held row (by simp [member])
    have globalEq : (global.endCall last.2).protectedTags=global.protectedTags.remove last.1 := by
      simp only [GlobalState.endCall,singleton]
      rfl
    rw [globalEq]
    simpa only [ProtectedTags.contains,
      GeneralBorrowProtectorCacheMap.remove_other global.protectedTags last.1 row.1 different] using before
  · intro row member
    obtain ⟨anchor,node,present,tagged,nodeTag,hidden⟩ := initial.nodes row (by simp [member])
    rw [same]
    exact ⟨anchor,node,present,tagged,nodeTag,hidden⟩

private theorem array_induct {α : Type} (P : Array α→Prop) (empty : P #[])
    (push : ∀xs x,P xs→P (xs.push x)) (xs : Array α) : P xs := by
  have aux : ∀rows : List α,P rows.reverse.toArray := by
    intro rows
    induction rows with
    | nil => exact empty
    | cons x rows ih => simpa using push rows.reverse.toArray x ih
  simpa using aux xs.toList.reverse

/-- Actual source release events execute all stored LIFO tree releases and
endCall operations. Their success follows from readable physical policy and
raw frame/node metadata, including sparse allocations after GC. -/
theorem run (id : AllocId) (frames : Array (BorTag × FrameState)) :
    ∀tree global root,(structural : State tree)→tree.roots=#[root]→
      (readable : Every (fun location=>GeneralBorrowPhysicalReadable.Profile tree location global.protectedTags) tree.locations)→
      (authority : GeneralBorrowStructuralHistoryRootAuthorityAt.Profile tree root)→
      Frames id tree global frames→
      let state : Snapshot := ⟨tree,global,frames⟩
      let actual := GeneralBorrowForestGeneratedTagHistory.run id state (List.replicate frames.size .release)
      actual.completed=true ∧ actual.state.frames=#[] ∧ State actual.state.tree ∧
        Every (fun location=>GeneralBorrowPhysicalReadable.Profile actual.state.tree location actual.state.global.protectedTags) actual.state.tree.locations ∧
        GeneralBorrowStructuralHistoryRootAuthorityAt.Profile actual.state.tree root ∧
        Released id state frames.size := by
  induction frames using array_induct with
  | empty =>
    intro tree global root structural roots readable authority metadata
    exact ⟨rfl,rfl,structural,readable,authority,True.intro⟩
  | push frames last ih =>
    intro tree global root structural roots readable authority metadata
    obtain ⟨anchor,node,present,tagged,nodeTag,hidden⟩ := metadata.nodes last (by simp)
    have held := metadata.held last (by simp)
    have nodeTagged : tree.indexOfTag node.tag=some anchor := by rw [nodeTag];exact tagged
    have nodeHeld : global.protectedTags.contains node.tag=true := by rw [nodeTag];exact held
    obtain ⟨depth⟩ := structural.depth
    have profile : Every (GeneralBorrowRootAuthorityReadableRelease.Profile tree global.protectedTags root) tree.locations := by
      intro position valid
      exact ⟨structural.forest _ _,readable position valid,authority position valid⟩
    obtain ⟨rootNode,rootPresent,_⟩ := structural.rootNodes root (by simp [roots])
    have operation := GeneralBorrowRootAuthorityReadableRelease.release tree global.protectedTags anchor root rootNode rootPresent node present nodeTagged nodeHeld hidden
      structural.fits depth structural.children roots structural.covered profile
    rw [nodeTag] at operation
    let next := (tree.releaseProtector last.1 global.protectedTags).tree
    have nextStructural := (GeneralBorrowStructuralHistoryFrames.release tree structural last.1 global.protectedTags).1
    have nextReadable : Every (fun location=>GeneralBorrowPhysicalReadable.Profile next location (global.endCall last.2).protectedTags) next.locations := by
      apply GeneralBorrowPhysicalReadableProtections.end_call
      intro position valid
      exact (operation.2.2 position valid).2.1
    have nextAuthority : GeneralBorrowStructuralHistoryRootAuthorityAt.Profile next root := by
      intro position valid
      exact (operation.2.2 position valid).2.2
    have nextFrames : Frames id next (global.endCall last.2) frames := remaining id tree global frames last metadata next operation.2.1
    have nextRoots : next.roots=#[root] := by change (tree.releaseProtector last.1 global.protectedTags).tree.roots=#[root];rw [operation.2.1];exact roots
    have later := ih next (global.endCall last.2) root nextStructural nextRoots nextReadable nextAuthority nextFrames
    have sourceStep : step id ⟨tree,global,frames.push last⟩ .release =
        ⟨⟨next,global.endCall last.2,frames⟩,true⟩ := by
      simp only [step,Array.back?_push,operation.1,beq_self_eq_true,↓reduceIte,Array.pop_push]
      rfl
    have trace : Released id (⟨tree,global,frames.push last⟩:Snapshot) (frames.push last).size := by
      rw [Array.size_push,Released]
      refine ⟨last.1,last.2,by simp,operation.1,?_⟩
      rw [sourceStep]
      exact later.2.2.2.2.2
    simpa only [Array.size_push,List.replicate_succ,GeneralBorrowForestGeneratedTagHistory.run,sourceStep,↓reduceIte] using
      And.intro later.1 (And.intro later.2.1 (And.intro later.2.2.1 (And.intro later.2.2.2.1 (And.intro later.2.2.2.2.1 trace))))
end DuplicatePrefix.GeneralBorrowPhysicalReadableAuthorityLifo
