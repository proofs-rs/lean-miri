import duplicate_prefix.CurrentCallEmptyTypedEntry
import duplicate_prefix.S03NonliveEmptyMetadata
namespace DuplicatePrefix.CurrentCallEmptyEntrySourceData
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter CandidateStableCallOwnership CandidateCurrentJointCall GeneralRangeMapState
open CurrentCallEmptyTypedEntry
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def Leaf (tree : BorrowTree) (tag : BorTag) : Prop :=
  ∃ index node,tree.indexOfTag tag=some index ∧ tree.nodeAt index=some node ∧ node.tag=tag ∧
    node.children=#[] ∧ node.isExposed=false ∧
    Every (fun row => (GeneralBorrowWildcardVirtualLeaf.effective row index node).accessed=false) tree.locations

def Data {options before tracker argument} (effect : Effect options before tracker argument) (machine : Before) : Prop :=
  match effect.allocation with
  | none => True
  | some id => (∃ info,machine.memory.getAllocInfo id=.ok info ∧ info.kind≠.liveData) ∨
      ∃ entry,machine.memory.live.find? (fun row=>row.1==id)=some (id,entry) ∧ Leaf entry.allocation.extra tracker.global.nextPointerTag

private theorem pool_leaf {tree : BorrowTree} {parentTag tag : BorTag}
    (packet : ConcreteEmptyPoolEntry.Input tree parentTag tag) : Leaf packet.after tag := by
  obtain ⟨node,present,nodeTag,_,children,_,hidden⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields
    packet.stage packet.parent .None packet.index (GeneralBorrowFreshChild.child tag packet.parent) packet.stage_new
  have mapped : packet.after.indexOfTag tag=some packet.index := by
    unfold BorrowTree.indexOfTag
    rw [packet.mapping_after]
    exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag packet.fresh packet.index packet.free
  refine ⟨packet.index,node,mapped,present,nodeTag,children,hidden,?_⟩
  intro cursor valid
  have clean := packet.future_clean packet.index packet.clean cursor valid
  simp only [GeneralBorrowWildcardVirtualLeaf.effective,clean,Option.getD_none,TreeNode.defaultLocationState]

private theorem slot_leaf (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    Leaf (slot.after tag) tag := by
  refine ⟨slot.index,WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None,
    GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag fresh slot.index slot.free,
    GeneralBorrowFreshLocation.get_same tree.nodes slot.index _,rfl,rfl,rfl,?_⟩
  intro cursor valid
  have empty := clean slot.index slot.vacant cursor valid
  change ((tree.locations.entries[cursor].data.perms.get slot.index).getD _).accessed=false
  rw [empty];rfl

private theorem lazy_leaf (root tag : BorTag) (size : Size) (distinct : root≠tag) :
    Leaf (TypedRetagConcreteEmpty.lazyTree root tag size.bytes) tag := by
  refine ⟨⟨1⟩,_,BorrowRangeAccess.canonical_child_index root tag _ distinct,by rfl,rfl,rfl,rfl,?_⟩
  intro cursor valid
  dsimp only [TypedRetagConcreteEmpty.lazyTree,BorrowRangeAccess.canonicalChildTree] at valid ⊢
  unfold DedupRangeMap.new at valid ⊢
  by_cases zero : size.bytes==0
  · simp only [Size.ofBytes,zero,↓reduceIte,Array.size_empty,Nat.not_lt_zero] at valid
  · simp only [Size.ofBytes,zero,Bool.false_eq_true,↓reduceIte,Array.size_singleton] at valid ⊢
    have cursorEq : cursor=0 := by omega
    subst cursor
    rfl
private theorem live_runtime {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) :
    DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global := by
  have inWorld : Present (ActualWorld before) id entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
  exact (CandidateCurrentLiveRuntime.live options limits remaining before tracker 0 input.machine.state input.machine.resources id entry.allocation inWorld).1

private theorem concrete_live {options limits remaining span before tracker address id parent place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker
      (.pointer (Pointer.new (.concrete id parent) (Size.ofBytes address))) 0 place call data)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (child : CurrentCallEmptyTypedEntryConcrete.ChildEffect before id parent address entry tracker.global.nextPointerTag tree) :
    Leaf tree tracker.global.nextPointerTag := by
  have candidate := CurrentCallEmptyTypedEntryInteger.empty_candidate input
  change address≠0 ∧ DuplicatePrefixEmptyReferenceInput.Concrete
    (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses id parent at candidate
  have parentPresent : DuplicatePrefixEmptyReferenceInput.Parent entry.allocation.extra (some parent) := by
    rcases ConcreteEmptyCandidateDispatch.target_cases _ _ _ id parent candidate.2.2 with liveCase | nonliveCase | imageCase
    · obtain ⟨old,found,parent⟩ := liveCase
      have same := congrArg Prod.snd (Option.some.inj (found.symm.trans live))
      dsimp only at same
      subst old;exact parent
    · rw [live] at nonliveCase;cases nonliveCase.2
    · obtain ⟨_,_,absent,_⟩ := imageCase
      rw [live] at absent;contradiction
  obtain ⟨index,node,tagged,present⟩ := parentPresent
  have runtime := live_runtime input id entry live
  have fresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag := by
    intro row member;exact GeneralBorrowForestTagHighWater.different _ _ (runtime.below.mapping row member)
  have accounting := runtime.formed.allocator.accounting
  have fits : entry.allocation.extra.tagMapping.mapping.size≤4294967295 := by
    have bounds := input.machine.resources.nodeRoom (id,entry) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live))
    dsimp only at bounds
    unfold GeneralBorrowFreshStagePool.Accounting at accounting;omega
  let packet := ConcreteEmptyPoolEntry.factory entry.allocation.extra parent tracker.global.nextPointerTag index node
    (Classical.choice runtime.formed.depth) tagged present fresh runtime.formed.allocator.pool accounting fits
    (DuplicatePrefixBorrowContract.vacant_clean runtime)
  obtain ⟨base,offset,_,_,actual⟩ := child
  have operation := packet.child offset
  have equal : packet.after=tree := congrArg (fun result=>result.tree)
    (operation.symm.trans (by simpa only [GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation] using actual))
  rw [←equal];exact pool_leaf packet

private theorem wildcard_image_leaf (root tag : BorTag) (size : Size) (distinct : root≠tag) :
    Leaf (WildcardGlobalEmptyReferenceReborrow.finalTree root tag size) tag := by
  apply slot_leaf (BorrowTree.new root size) (WildcardGlobalEmptyReferenceReborrow.rootSlot root size) tag
  · intro row member
    simp [BorrowTree.new] at member
    subst row;exact distinct
  · exact GeneralBorrowGcVacantClean.initial root size

/-- Finite data dispatch on the actual empty-source Effect allocation. The
resultMachine memory is also exactly the afterArgumentsMachine memory. -/
theorem of_effect {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (effect : Effect options before tracker argument)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (localId : MIR.LocalId) (valid : localId<frame.locals.size) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    Data effect (resultMachine effect fresh remaining span frames frame borrowFrame localId valid) := by
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  cases effect with
  | integer address => trivial
  | miss address missing => trivial
  | concreteLive address id parent entry tree live child =>
    right
    refine ⟨{entry with allocation:=entry.allocation.setExtra tree},?_,concrete_live input entry tree live child⟩
    exact StackPopRelease.lookup_commit_same before.memory id entry tree
  | wildcardLive address hit entry tree live child =>
    right
    refine ⟨{entry with allocation:=entry.allocation.setExtra tree},?_,?_⟩
    · exact StackPopRelease.lookup_commit_same before.memory hit.id entry tree
    · obtain ⟨slot,rfl⟩ := child
      have runtime := live_runtime input hit.id entry live
      apply slot_leaf entry.allocation.extra slot tracker.global.nextPointerTag
      · intro row member;exact GeneralBorrowForestTagHighWater.different _ _ (runtime.below.mapping row member)
      · exact DuplicatePrefixBorrowContract.vacant_clean runtime
  | concreteNonlive address id parent metadata absent =>
    left
    exact S03NonliveEmptyMetadata.known before.memory id (some parent) metadata absent
  | wildcardNonlive address hit metadata absent =>
    left
    exact S03NonliveEmptyMetadata.known before.memory hit.id none metadata absent
  | concreteImage address id parent image source converted descriptor attributes =>
    right
    obtain ⟨packet⟩ := S03MaterializableInput.of_input options before tracker id (some parent) image input.machine.resources.cachedRootsBelow
    have rootEq : parent=packet.root := by
      rcases packet.agreement with impossible | equal
      · contradiction
      · exact Option.some.inj equal
    have distinct : parent≠tracker.global.nextPointerTag := by rw [rootEq];exact packet.distinct
    let initial : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
      ⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new parent source.byteSize)⟩
    refine ⟨{initial with allocation:=initial.allocation.setExtra (TypedRetagConcreteEmpty.lazyTree parent tracker.global.nextPointerTag source.byteSize.bytes)},?_,lazy_leaf parent tracker.global.nextPointerTag source.byteSize distinct⟩
    exact StackPopRelease.lookup_commit_same _ id initial _
  | wildcardImage address hit image root source converted rootCached descriptor attributes =>
    right
    obtain ⟨packet⟩ := S03MaterializableInput.of_input options before tracker hit.id none image input.machine.resources.cachedRootsBelow
    have rootEq : root=packet.root := Option.some.inj (rootCached.symm.trans packet.rootCached)
    have distinct : root≠tracker.global.nextPointerTag := by rw [rootEq];exact packet.distinct
    let initial : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
      ⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)⟩
    refine ⟨{initial with allocation:=initial.allocation.setExtra (WildcardGlobalEmptyReferenceReborrow.finalTree root tracker.global.nextPointerTag source.byteSize)},?_,wildcard_image_leaf root tracker.global.nextPointerTag source.byteSize distinct⟩
    exact StackPopRelease.lookup_commit_same _ hit.id initial _

end
end DuplicatePrefix.CurrentCallEmptyEntrySourceData
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntrySourceData" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved empty source data dependency {dependency}"
