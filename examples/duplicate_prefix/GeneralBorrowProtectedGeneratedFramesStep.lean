import duplicate_prefix.GeneralBorrowGcLiveRetained
import duplicate_prefix.GeneralBorrowProtectedGeneratedFramesNodes
import duplicate_prefix.GeneralBorrowForestGeneratedReadablePrepared
import duplicate_prefix.GeneralBorrowPhysicalReadableLifo
namespace DuplicatePrefix.GeneralBorrowProtectedGeneratedFramesStep
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowPhysicalReadableLifo GeneralBorrowForestGeneratedHiddenCache
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

structure Formed (id : AllocId) (root : UniIndex) (state : Snapshot) : Prop where
  cache : GeneralBorrowForestGeneratedCacheHistoryStep.Formed state
  frames : Frames id state.tree state.global state.frames
  roots : state.tree.roots = #[root]

private theorem transport (id : AllocId) (before after : BorrowTree) (oldGlobal nextGlobal : GlobalState)
    (frames : Array (BorTag × FrameState)) (metadata : Frames id before oldGlobal frames)
    (held : ∀ row ∈ frames.toList,nextGlobal.protectedTags.contains row.1 = true)
    (nodes : ∀ query old,before.nodeAt query = some old → oldGlobal.protectedTags.contains old.tag = true → ∃ next,after.nodeAt query = some next ∧ next.tag = old.tag)
    (tagged : GeneralBorrowGcAllocator.NodeTags after) (hidden : Hidden after) : Frames id after nextGlobal frames := by
  refine ⟨metadata.singleton,metadata.distinct,held,?_⟩
  intro row member
  obtain ⟨query,node,present,_,tag,_⟩ := metadata.nodes row member
  obtain ⟨next,found,same⟩ := nodes query node present (by rw [tag];exact metadata.held row member)
  have lookup := tagged query next found
  have value : next.tag = row.1 := same.trans tag
  exact ⟨query,next,found,by simpa only [BorrowTree.indexOfTag,value] using lookup,value,hidden query next found⟩

private theorem push (id : AllocId) (tree : BorrowTree) (global : GlobalState) (frames : Array (BorTag × FrameState))
    (metadata : Frames id tree global frames) (tag : BorTag) (frame : FrameState)
    (singleton : frame.protectedTags = #[(id,tag)])
    (fresh : ∀ row ∈ frames.toList,row.1 ≠ tag) (held : global.protectedTags.contains tag = true)
    (node : ∃ query node,tree.nodeAt query = some node ∧ tree.indexOfTag tag = some query ∧ node.tag = tag ∧ node.isExposed = false) :
    Frames id tree global (frames.push (tag,frame)) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro row member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with before | same
    · exact metadata.singleton row before
    · subst row;exact singleton
  · simp only [Array.toList_push,List.map_append,List.map_singleton]
    apply List.nodup_append.mpr
    refine ⟨metadata.distinct,by simp,?_⟩
    intro left member right last equal
    have rightEq : right = tag := by simpa only [List.mem_singleton] using last
    obtain ⟨row,present,value⟩ := List.mem_map.mp member
    exact fresh row present (value.trans (equal.trans rightEq))
  · intro row member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with before | same
    · exact metadata.held row before
    · subst row;exact held
  · intro row member
    simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with before | same
    · exact metadata.nodes row before
    · subst row;exact node

private theorem held_live (protections : ProtectedTags) (live : Array BorTag)
    (guard : ∀ row ∈ protections.entries,live.contains row.1 = true) (tag : BorTag)
    (held : protections.contains tag = true) : live.contains tag = true := by
  unfold ProtectedTags.contains ProtectedTags.get at held
  cases found : protections.entries.find? (fun row => row.1 == tag) with
  | none => simp [found] at held
  | some row =>
    have member := Array.mem_of_find?_eq_some found
    have same : row.1 = tag := by simpa only [beq_iff_eq] using Array.find?_some found
    rw [←same]
    exact guard row member

private theorem constructor (id : AllocId) (root : UniIndex) (state : Snapshot) (initial : Formed id root state)
    (parentTag : BorTag) (base : Size) (inside : DedupRangeMap LocationState) (outside : Permission) (held : Bool)
    (allowed : GeneralBorrowForestGeneratedReadableHistory.Applicable state (.constructor (.concrete parentTag) base inside outside held))
    (nextCache : GeneralBorrowForestGeneratedCacheHistoryStep.Formed (step id state (.constructor (.concrete parentTag) base inside outside held)).state) :
    Frames id (step id state (.constructor (.concrete parentTag) base inside outside held)).state.tree
      (step id state (.constructor (.concrete parentTag) base inside outside held)).state.global
      (step id state (.constructor (.concrete parentTag) base inside outside held)).state.frames ∧
      (step id state (.constructor (.concrete parentTag) base inside outside held)).state.tree.roots = #[root] := by
  obtain ⟨room,nodeRoom,parentData,initialOutside,notUnique,⟨sifa,foreign⟩,bounded,insideInitial⟩ := allowed.1.1
  obtain ⟨parent,parentNode,parentTagged,parentPresent⟩ := parentData
  have flags := GeneralBorrowForestGeneratedTagHistoryFlags.generated id state initial.cache.sifa.generated room held
  have fresh := GeneralBorrowForestGeneratedTagHistoryData.fresh state initial.cache.sifa.generated
  let actual := (state.tree.newChild base (.concrete parentTag) state.global.nextPointerTag inside outside held).tree
  let allocated : GlobalState := {state.global with nextPointerTag := TypedRetagEmpty.successorTag state.global.nextPointerTag room}
  let registered := register id state allocated state.global.nextPointerTag held
  have source : (step id state (.constructor (.concrete parentTag) base inside outside held)).state = {registered with tree := actual} := by
    simp only [step,flags.1];rfl
  have nodes := GeneralBorrowProtectedGeneratedFramesNodes.constructor state.tree initial.cache.sifa.generated.structural parentTag parent parentNode
    parentTagged parentPresent state.global.nextPointerTag fresh nodeRoom outside sifa held initialOutside notUnique foreign base inside
  have tags : GeneralBorrowGcAllocator.NodeTags actual := by simpa only [step,flags.1] using nextCache.sifa.generated.structural.allocator.nodeTags
  have hidden : Hidden actual := by simpa only [step,flags.1] using nextCache.empty.hidden
  have newTagFresh : ∀ row ∈ state.frames.toList,row.1 ≠ state.global.nextPointerTag := by
    intro row member same
    have before := initial.frames.held row member
    rw [same,GeneralBorrowForestGeneratedTagHistoryFlags.counter_unheld state initial.cache.sifa.generated] at before
    cases before
  refine ⟨?_,?_⟩
  · rw [source]
    cases held with
    | false =>
      change Frames id actual allocated state.frames
      exact transport id state.tree actual state.global allocated state.frames initial.frames initial.frames.held (fun query old present _ => nodes.1 query old present) tags hidden
    | true =>
      let added := allocated.addProtector {} id state.global.nextPointerTag .StrongProtector
      change Frames id actual added.1 (state.frames.push (state.global.nextPointerTag,added.2))
      have oldHeld : ∀ row ∈ state.frames.toList,added.1.protectedTags.contains row.1 = true := by
        intro row member
        change (state.global.protectedTags.insert state.global.nextPointerTag .StrongProtector).contains row.1 = true
        unfold ProtectedTags.contains
        rw [GeneralBorrowProtectorCacheMap.insert_other _ state.global.nextPointerTag row.1 .StrongProtector (newTagFresh row member)]
        exact initial.frames.held row member
      have before := transport id state.tree actual state.global added.1 state.frames initial.frames oldHeld (fun query old present _ => nodes.1 query old present) tags hidden
      obtain ⟨query,node,present,value⟩ := nodes.2.1
      have lookup := tags query node present
      have current : ∃ query node,actual.nodeAt query = some node ∧ actual.indexOfTag state.global.nextPointerTag = some query ∧
          node.tag = state.global.nextPointerTag ∧ node.isExposed = false :=
        ⟨query,node,present,by simpa only [BorrowTree.indexOfTag,value] using lookup,value,hidden query node present⟩
      exact push id actual added.1 state.frames before state.global.nextPointerTag added.2 rfl newTagFresh
        (by simp [added,GlobalState.addProtector,ProtectedTags.contains]) current
  · rw [source]
    exact nodes.2.2.trans initial.roots

/-- Raw concrete constructor/GC source guards form every captured frame's
singleton shape, distinct held key, actual present tagged hidden node and the
original singleton roots. No after-step frame or node premise is supplied. -/
theorem preserves (id : AllocId) (root : UniIndex) (state : Snapshot) (initial : Formed id root state)
    (event : Event) (allowed : GeneralBorrowForestGeneratedReadableHistory.Applicable state event) :
    (step id state event).completed = true ∧ Formed id root (step id state event).state := by
  have next := GeneralBorrowForestGeneratedCacheHistoryStep.preserves id state initial.cache event
    (GeneralBorrowForestGeneratedReadablePrepared.cache_guard state event allowed)
  refine ⟨next.1,next.2,?_,?_⟩
  cases event with
  | access source offset len kind mode => exact False.elim allowed.1.2
  | release => exact False.elim allowed.1.2
  | allocate =>
    have actual := TypedRetagEmpty.allocate_tag state.global allowed.1.1
    simp only [step,actual]
    exact ⟨initial.frames.singleton,initial.frames.distinct,initial.frames.held,initial.frames.nodes⟩
  | constructor parent base inside outside held =>
    cases parent with
    | wildcard => exact False.elim allowed.2
    | concrete tag => exact (constructor id root state initial tag base inside outside held allowed next.2).1
  | gc live =>
    change Frames id (state.tree.removeUnreachableTags live).tree state.global state.frames
    apply transport id state.tree _ state.global state.global state.frames initial.frames initial.frames.held _ next.2.sifa.generated.structural.allocator.nodeTags next.2.empty.hidden
    intro query node present held
    exact GeneralBorrowGcLiveRetained.collect state.tree live query node present (held_live _ _ allowed.1.1 node.tag held)
  all_goals cases event with
  | access source offset len kind mode => exact False.elim allowed.1.2
  | release => exact False.elim allowed.1.2
  | allocate => have actual := TypedRetagEmpty.allocate_tag state.global allowed.1.1;simpa only [step,actual] using initial.roots
  | constructor parent base inside outside held => cases parent with
    | wildcard => exact False.elim allowed.2
    | concrete tag => exact (constructor id root state initial tag base inside outside held allowed next.2).2
  | gc live =>
    have frame := GeneralBorrowGcResourceFrame.preserves (n := 0) (fun index => Fin.elim0 index) state.tree live (by intro index;exact Fin.elim0 index)
    exact frame.roots.trans initial.roots
end DuplicatePrefix.GeneralBorrowProtectedGeneratedFramesStep
