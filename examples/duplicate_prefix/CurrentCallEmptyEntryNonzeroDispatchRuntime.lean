import duplicate_prefix.CurrentCallEmptyEntryNonzeroDispatchState
import duplicate_prefix.CurrentCallEmptyEntrySourceData
import duplicate_prefix.S03MaterializableRootRuntime
import duplicate_prefix.S04ZeroConcreteRuntime
import duplicate_prefix.S04ZeroWildcardRuntime
namespace DuplicatePrefix.CurrentCallEmptyEntryNonzeroDispatchRuntime
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallEmptyTypedEntry
open GeneralBorrowFnEntryRegistration CurrentCallEmptyEntryNonzeroDispatchState
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem live_runtime {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) :
    DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global := by
  have inWorld : Present (ActualWorld before) id entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(id,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
  exact (CandidateCurrentLiveRuntime.live options limits remaining before tracker 0 input.machine.state input.machine.resources id entry.allocation inWorld).1

private theorem concrete_parent {options limits remaining span before tracker address id parent place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker
      (.pointer (Pointer.new (.concrete id parent) (Size.ofBytes address))) 0 place call data)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry)) :
    DuplicatePrefixEmptyReferenceInput.Parent entry.allocation.extra (some parent) := by
  have candidate := CurrentCallEmptyTypedEntryInteger.empty_candidate input
  change address≠0 ∧ DuplicatePrefixEmptyReferenceInput.Concrete
    (DuplicatePrefixCallSpecification.imageContext options before tracker) before.memory before.user.addresses id parent at candidate
  rcases ConcreteEmptyCandidateDispatch.target_cases _ _ _ id parent candidate.2.2 with liveCase | nonliveCase | imageCase
  · obtain ⟨old,found,parent⟩ := liveCase
    have same := congrArg Prod.snd (Option.some.inj (found.symm.trans live))
    dsimp only at same
    subst old;exact parent
  · rw [live] at nonliveCase;cases nonliveCase.2
  · obtain ⟨_,_,absent,_⟩ := imageCase
    rw [live] at absent;contradiction

private theorem image_root_runtime {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (id : AllocId) (root : BorTag) (size : Size)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (rootBelow : root.value.toNat<tracker.global.nextPointerTag.value.toNat) :
    DuplicatePrefixBorrowContract.RuntimeFacts (BorrowTree.new root size) (registered tracker.global {} id fresh).1 := by
  obtain ⟨allocation,present,_⟩ := input.actual.returnValue
  have original := (CandidateCurrentLiveRuntime.live options limits remaining before tracker 0 input.machine.state input.machine.resources
    call.returnId allocation present).1
  have current := (GeneralBorrowFnEntryRegistrationRuntime.prepare allocation.extra tracker.global {} id fresh original).2.2.2.1
  have step := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
  apply S03MaterializableRootRuntime.initial root size.bytes (registered tracker.global {} id fresh).1
  · change root.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
    omega
  · exact current.below.protectors

private theorem tag_step (global : GlobalState) (id : AllocId)
    (fresh : global.nextPointerTag.value<18446744073709551615) :
    global.nextPointerTag.value.toNat<(registered global {} id fresh).1.nextPointerTag.value.toNat := by
  have step := GenericFunctionEntryNumerics.successor_value global.nextPointerTag fresh
  change global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag global.nextPointerTag fresh).value.toNat
  omega

private theorem held_tag (global : GlobalState) (id : AllocId)
    (fresh : global.nextPointerTag.value<18446744073709551615) :
    (registered global {} id fresh).1.protectedTags.contains global.nextPointerTag=true := by
  unfold ProtectedTags.contains
  rw [show (registered global {} id fresh).1.protectedTags.get global.nextPointerTag=some .StrongProtector from ProtectedTags.get_insert_same _ _ _]
  rfl

/-- Current source data after actual empty argument copy, before Bool entry. -/
theorem stage {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (effect : Effect options before tracker argument)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (localId : MIR.LocalId) (valid : localId<frame.locals.size) (id : AllocId) (allocated : effect.allocation=some id) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    let machine := resultMachine effect fresh remaining span frames frame borrowFrame localId valid
    let current := (CurrentCallEmptyEntryArguments.nextTracker effect fresh).global
    (∃ metadataTag,DuplicatePrefixEmptyReferenceInput.Metadata machine.memory id metadataTag ∧
      machine.memory.live.find? (fun row=>row.1==id)=none) ∨
    ∃ entry,machine.memory.live.find? (fun row=>row.1==id)=some (id,entry) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra current ∧ entry.allocation.extra.nodes.size+8<65536 := by
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  cases effect with
  | integer address => cases allocated
  | miss address missing => cases allocated
  | concreteNonlive address sourceId parent metadata absent =>
    have equal : sourceId=id := Option.some.inj allocated
    subst id
    exact .inl ⟨some parent,metadata,absent⟩
  | wildcardNonlive address hit metadata absent =>
    have equal : hit.id=id := Option.some.inj allocated
    subst id
    exact .inl ⟨none,metadata,absent⟩
  | concreteLive address sourceId parent entry tree live child =>
    have equal : sourceId=id := Option.some.inj allocated
    subst id
    have original := live_runtime input sourceId entry live
    have current := (GeneralBorrowFnEntryRegistrationRuntime.prepare entry.allocation.extra tracker.global {} sourceId fresh original).2.2.2.1
    obtain ⟨parentIndex,parentNode,tagged,parentAt⟩ := concrete_parent input entry live
    have tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag := by
      intro row member;exact GeneralBorrowForestTagHighWater.different _ _ (original.below.mapping row member)
    have margin := input.machine.resources.nodeRoom (sourceId,entry) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live))
    dsimp only at margin
    obtain ⟨base,offset,_,_,actual⟩ := child
    have result := S04ZeroConcreteRuntime.construct entry.allocation.extra (registered tracker.global {} sourceId fresh).1 current parent parentIndex parentNode
      tagged parentAt tracker.global.nextPointerTag tagFresh (by omega) (tag_step _ _ _) (held_tag _ _ _) offset
    have actual' : entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parent) tracker.global.nextPointerTag
        (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true=⟨tree,.ok ()⟩ := by
      simpa only [ChildBorrow.fnEntryLocation,GeneralBorrowFreshChild.inside] using actual
    rw [actual'] at result
    refine .inr ⟨{entry with allocation:=entry.allocation.setExtra tree},StackPopRelease.lookup_commit_same _ _ _ _,result.2.1,?_⟩
    have growth := result.2.2.2
    change tree.nodes.size≤entry.allocation.extra.nodes.size+1 at growth
    change tree.nodes.size+8<65536
    omega
  | wildcardLive address hit entry tree live child =>
    have equal : hit.id=id := Option.some.inj allocated
    subst id
    have original := live_runtime input hit.id entry live
    have current := (GeneralBorrowFnEntryRegistrationRuntime.prepare entry.allocation.extra tracker.global {} hit.id fresh original).2.2.2.1
    have tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag := by
      intro row member;exact GeneralBorrowForestTagHighWater.different _ _ (original.below.mapping row member)
    have margin := input.machine.resources.nodeRoom (hit.id,entry) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live))
    dsimp only at margin
    obtain ⟨slot,rfl⟩ := child
    have result := S04ZeroWildcardRuntime.construct entry.allocation.extra (registered tracker.global {} hit.id fresh).1 current tracker.global.nextPointerTag
      tagFresh (by omega) (tag_step _ _ _) (held_tag _ _ _) 0
    rw [slot.child tracker.global.nextPointerTag tagFresh 0] at result
    refine .inr ⟨{entry with allocation:=entry.allocation.setExtra (slot.after tracker.global.nextPointerTag)},StackPopRelease.lookup_commit_same _ _ _ _,result.2.1,?_⟩
    have growth := result.2.2.2
    change (slot.after tracker.global.nextPointerTag).nodes.size≤entry.allocation.extra.nodes.size+1 at growth
    change (slot.after tracker.global.nextPointerTag).nodes.size+8<65536
    omega
  | concreteImage address sourceId parent image source converted descriptor attributes =>
    have equal : sourceId=id := Option.some.inj allocated
    subst id
    obtain ⟨packet⟩ := S03MaterializableInput.of_input options before tracker sourceId (some parent) image input.machine.resources.cachedRootsBelow
    have rootEq : parent=packet.root := by
      rcases packet.agreement with impossible | equal
      · contradiction
      · exact Option.some.inj equal
    have distinct : parent≠tracker.global.nextPointerTag := by rw [rootEq];exact packet.distinct
    have below : parent.value.toNat<tracker.global.nextPointerTag.value.toNat := by rw [rootEq];exact packet.rootBelow
    have initial := image_root_runtime input sourceId parent source.byteSize fresh below
    have tagFresh : GeneralBorrowTagMap.Fresh (BorrowTree.new parent source.byteSize).tagMapping tracker.global.nextPointerTag := by
      intro row member
      simp [BorrowTree.new] at member
      subst row;exact distinct
    have present : (BorrowTree.new parent source.byteSize).nodeAt ⟨0⟩=some {tag:=parent,parent:=none,children:=#[],defaultInitialPermission:=.Disabled,defaultInitialSifa:=.None,isExposed:=false} := by rfl
    have tagged : (BorrowTree.new parent source.byteSize).indexOfTag parent=some ⟨0⟩ := by
      simp [BorrowTree.new,BorrowTree.indexOfTag,UniKeyMap.get]
      rfl
    have result := S04ZeroConcreteRuntime.construct (BorrowTree.new parent source.byteSize) (registered tracker.global {} sourceId fresh).1 initial
      parent ⟨0⟩ _ tagged present tracker.global.nextPointerTag tagFresh (by change 1+1≤4294967295;decide) (tag_step _ _ _) (held_tag _ _ _) 0
    have ctor := ChildConstructor.new_child_zero_exact parent tracker.global.nextPointerTag distinct source.byteSize.bytes 0
    change (BorrowTree.new parent source.byteSize).newChild (Size.ofBytes 0) (.concrete parent) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 0) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true=
      ⟨TypedRetagConcreteEmpty.lazyTree parent tracker.global.nextPointerTag source.byteSize.bytes,.ok ()⟩ at ctor
    rw [ctor] at result
    let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind := ⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new parent source.byteSize)⟩
    refine .inr ⟨{entry with allocation:=entry.allocation.setExtra (TypedRetagConcreteEmpty.lazyTree parent tracker.global.nextPointerTag source.byteSize.bytes)},
      StackPopRelease.lookup_commit_same _ _ _ _,result.2.1,?_⟩
    have growth := result.2.2.2
    change (TypedRetagConcreteEmpty.lazyTree parent tracker.global.nextPointerTag source.byteSize.bytes).nodes.size+8<65536
    change (TypedRetagConcreteEmpty.lazyTree parent tracker.global.nextPointerTag source.byteSize.bytes).nodes.size≤1+1 at growth
    omega
  | wildcardImage address hit image root source converted rootCached descriptor attributes =>
    have equal : hit.id=id := Option.some.inj allocated
    subst id
    obtain ⟨packet⟩ := S03MaterializableInput.of_input options before tracker hit.id none image input.machine.resources.cachedRootsBelow
    have rootEq : root=packet.root := Option.some.inj (rootCached.symm.trans packet.rootCached)
    have distinct : root≠tracker.global.nextPointerTag := by rw [rootEq];exact packet.distinct
    have below : root.value.toNat<tracker.global.nextPointerTag.value.toNat := by rw [rootEq];exact packet.rootBelow
    have initial := image_root_runtime input hit.id root source.byteSize fresh below
    have tagFresh : GeneralBorrowTagMap.Fresh (BorrowTree.new root source.byteSize).tagMapping tracker.global.nextPointerTag := by
      intro row member
      simp [BorrowTree.new] at member
      subst row;exact distinct
    let slot := WildcardGlobalEmptyReferenceReborrow.rootSlot root source.byteSize
    have result := S04ZeroWildcardRuntime.construct (BorrowTree.new root source.byteSize) (registered tracker.global {} hit.id fresh).1 initial
      tracker.global.nextPointerTag tagFresh (by change 1+1≤4294967295;decide) (tag_step _ _ _) (held_tag _ _ _) 0
    rw [slot.child tracker.global.nextPointerTag tagFresh 0] at result
    let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind := ⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)⟩
    refine .inr ⟨{entry with allocation:=entry.allocation.setExtra (slot.after tracker.global.nextPointerTag)},
      StackPopRelease.lookup_commit_same _ _ _ _,result.2.1,?_⟩
    have growth := result.2.2.2
    change (slot.after tracker.global.nextPointerTag).nodes.size+8<65536
    change (slot.after tracker.global.nextPointerTag).nodes.size≤1+1 at growth
    omega
private theorem memory_eq {options limits remaining span before tracker argument place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data}
    (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) :
    (machine out count).memory = {(sourceMachine out).memory with live := ((sourceMachine out).memory.live.filter (fun row => row.1 != out.physical.id)).push (out.physical.id,{out.physical.entry with allocation:=out.updated})} := by
  exact MemoryCopyBridge.live_update_twice (sourceMachine out).memory out.physical.id
    {out.physical.entry with allocation:=out.physical.entry.allocation.setExtra out.certificate.output.child.tree}
    {out.physical.entry with allocation:=out.updated}

private theorem live_other {options limits remaining span before tracker argument place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data}
    (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (different : id≠out.physical.id)
    (live : (sourceMachine out).memory.live.find? (fun row=>row.1==id)=some (id,entry)) :
    (machine out count).memory.live.find? (fun row=>row.1==id)=some (id,entry) := by
  rw [memory_eq]
  simpa only [StackPopRelease.commitTree,RetagEntry.updatedMemory,Allocation.setExtra,Allocation.mapExtra] using
    StackPopRelease.lookup_commit_other (sourceMachine out).memory out.physical.id id
      {out.physical.entry with allocation:=out.updated} entry out.updated.extra different live

private theorem leaf_of_live {options limits remaining span before tracker argument place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data}
    (out : CurrentCallEmptyEntryRoot.Output input #[]) (id : AllocId) (allocated : out.effect.allocation=some id)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : (sourceMachine out).memory.live.find? (fun row=>row.1==id)=some (id,entry)) :
    CurrentCallEmptyEntrySourceData.Leaf entry.allocation.extra tracker.global.nextPointerTag := by
  have known := CurrentCallEmptyEntrySourceData.of_effect (CurrentCallPush.prepared_input input #[]) out.effect #[]
    (EmptyRootArguments.firstLive (root input)).frame {} 1 ((EmptyRootArguments.firstLive (root input)).valid EmptyRootArguments.i1)
  change CurrentCallEmptyEntrySourceData.Data out.effect (sourceMachine out) at known
  simp only [CurrentCallEmptyEntrySourceData.Data,allocated] at known
  rcases known with ⟨info,information,nonlive⟩ | ⟨other,otherLive,leaf⟩
  · rw [MemoryState.getAllocInfo,live] at information
    cases information
    exact False.elim (nonlive rfl)
  · have same : other=entry := (Prod.mk.inj (Option.some.inj (otherLive.symm.trans live))).2
    subst other;exact leaf

/-- Source rows on the other physical allocation retain their actual runtime
through fresh Bool registration and the one-row physical replacement. -/
theorem other_source {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) (id : AllocId)
    (allocated : out.effect.allocation=some id) (different : id≠out.physical.id) :
    (∃ metadataTag,DuplicatePrefixEmptyReferenceInput.Metadata (machine out count).memory id metadataTag ∧
      (machine out count).memory.live.find? (fun row=>row.1==id)=none) ∨
    ∃ entry,(machine out count).memory.live.find? (fun row=>row.1==id)=some (id,entry) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra (held out).global ∧
      entry.allocation.extra.nodes.size+2≤4294967295 ∧
      ∃ index node,entry.allocation.extra.indexOfTag tracker.global.nextPointerTag=some index ∧ entry.allocation.extra.nodeAt index=some node := by
  have original := stage (CurrentCallPush.prepared_input input #[]) out.effect #[]
    (EmptyRootArguments.firstLive (root input)).frame {} 1 ((EmptyRootArguments.firstLive (root input)).valid EmptyRootArguments.i1) id allocated
  change (∃ metadataTag,DuplicatePrefixEmptyReferenceInput.Metadata (sourceMachine out).memory id metadataTag ∧
      (sourceMachine out).memory.live.find? (fun row=>row.1==id)=none) ∨
    ∃ entry,(sourceMachine out).memory.live.find? (fun row=>row.1==id)=some (id,entry) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra (sourceTracker out).global ∧ entry.allocation.extra.nodes.size+8<65536 at original
  rcases original with ⟨metadataTag,metadata,absent⟩ | ⟨entry,live,runtime,margin⟩
  · left
    rw [memory_eq]
    exact ⟨metadataTag,S03NonliveEmptyMetadata.replace (sourceMachine out).memory id out.physical.id metadataTag
      {out.physical.entry with allocation:=out.updated} metadata absent (Ne.symm different),
      S03NonliveEmptyMetadata.live_replace_absent (sourceMachine out).memory id out.physical.id
        {out.physical.entry with allocation:=out.updated} absent (Ne.symm different)⟩
  · right
    have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra (held out).global := by
      rw [held_global]
      exact (GeneralBorrowFnEntryRegistrationRuntime.prepare entry.allocation.extra (sourceTracker out).global
        (CurrentCallEmptyEntryBool.rootSource out.effect) out.physical.id out.room runtime).2.2.2.1
    obtain ⟨index,node,lookup,present,_⟩ := leaf_of_live out id allocated entry live
    exact ⟨entry,live_other out count id entry different live,afterRuntime,by omega,index,node,lookup,present⟩

/-- The original empty Candidate supplies the actual source cached base for
all allocated Effect variants, including lazy images and nonlive metadata. -/
theorem cached_source {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) (id : AllocId) (allocated : out.effect.allocation=some id) :
    ∃ base,(machine out count).user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩ := by
  rw [addresses]
  have original := CurrentCallPush.prepared_input input #[]
  cases effect : out.effect with
  | integer address => simp [effect,Effect.allocation] at allocated
  | miss address missing => simp [effect,Effect.allocation] at allocated
  | concreteLive address sourceId parent entry tree live child
  | concreteNonlive address sourceId parent metadata absent
  | concreteImage address sourceId parent image source converted descriptor attributes =>
    have sourceEq : sourceId=id := by simpa only [effect,Effect.allocation,Option.some.injEq] using allocated
    have candidate := CurrentCallEmptyTypedEntryInteger.empty_candidate original
    change address≠0 ∧ DuplicatePrefixEmptyReferenceInput.Concrete _ _ _ sourceId parent at candidate
    subst id
    exact candidate.2.1
  | wildcardLive address hit entry tree live child
  | wildcardNonlive address hit metadata absent
  | wildcardImage address hit image root source converted rootCached descriptor attributes =>
    have sourceEq : hit.id=id := by simpa only [effect,Effect.allocation,Option.some.injEq] using allocated
    subst id
    exact ⟨hit.base,hit.cached⟩

/-- Unified current source runtime from the ORIGINAL call and real entry. -/
theorem source {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) (facts : CurrentCallEmptyEntryRoot.Facts out count)
    (id : AllocId) (allocated : out.effect.allocation=some id) :
    (∃ metadataTag,DuplicatePrefixEmptyReferenceInput.Metadata (machine out count).memory id metadataTag ∧
      (machine out count).memory.live.find? (fun row=>row.1==id)=none) ∨
    ∃ entry,(machine out count).memory.live.find? (fun row=>row.1==id)=some (id,entry) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra (held out).global ∧
      entry.allocation.extra.nodes.size+2≤4294967295 ∧
      ∃ index node,entry.allocation.extra.indexOfTag tracker.global.nextPointerTag=some index ∧ entry.allocation.extra.nodeAt index=some node := by
  by_cases same : id=out.physical.id
  · have initial := stage (CurrentCallPush.prepared_input input #[]) out.effect #[]
      (EmptyRootArguments.firstLive (root input)).frame {} 1 ((EmptyRootArguments.firstLive (root input)).valid EmptyRootArguments.i1) id allocated
    change (∃ metadataTag,DuplicatePrefixEmptyReferenceInput.Metadata (sourceMachine out).memory id metadataTag ∧
        (sourceMachine out).memory.live.find? (fun row=>row.1==id)=none) ∨
      ∃ entry,(sourceMachine out).memory.live.find? (fun row=>row.1==id)=some (id,entry) ∧
        DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra (sourceTracker out).global ∧ entry.allocation.extra.nodes.size+8<65536 at initial
    have physicalLive : (sourceMachine out).memory.live.find? (fun row=>row.1==out.physical.id)=some (out.physical.id,out.physical.entry) := out.physical.live
    rcases initial with ⟨metadataTag,metadata,absent⟩ | ⟨entry,live,initialRuntime,margin⟩
    · rw [same,physicalLive] at absent
      cases absent
    · have entryEq : entry=out.physical.entry := by
        rw [same,physicalLive] at live
        exact (Prod.mk.inj (Option.some.inj live)).2.symm
      subst entry
      have extra : out.updated.extra=(CurrentCallEmptyEntryCompleteRelease.written out.certificate.output (UInt64.ofNat call.returnOffset)).tree :=
        facts.2.2.2.2.2.2.1
      have currentRuntime : DuplicatePrefixBorrowContract.RuntimeFacts out.updated.extra (held out).global := facts.2.2.2.2.2.2.2.1
      have growth := out.certificate.growth
      rw [←extra] at growth
      have leaf := out.certificate.qLeaf (allocated.trans (congrArg some same))
      rw [←extra] at leaf
      obtain ⟨index,node,lookup,present,_⟩ := leaf
      refine .inr ⟨{out.physical.entry with allocation:=out.updated},?_,currentRuntime,(by change out.updated.extra.nodes.size+2≤4294967295;omega),index,node,lookup,present⟩
      rw [same,memory_eq]
      exact MemoryCopyBridge.live_lookup_replaced (sourceMachine out).memory out.physical.id _
  · exact other_source input out count id allocated same

end
end DuplicatePrefix.CurrentCallEmptyEntryNonzeroDispatchRuntime

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryNonzeroDispatchRuntime" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved empty nonzero runtime dependency {dependency}"
