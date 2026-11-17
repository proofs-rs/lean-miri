import duplicate_prefix.CurrentCallResourceChildWrite
import duplicate_prefix.CandidateCurrentGrantRuntime
import duplicate_prefix.CurrentCallResourceBoolActivation

/-! Runtime and graph facts for the actual Bool child Write and its heap
installation. No whole storage/provenance invariant is asserted after clearing
Bool provenance; physical mask/size and DirectInput facts remain separate. -/
namespace DuplicatePrefix.CurrentCallBoolWriteRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowFnEntryRegistration
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

theorem child_write_runtime {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (start amount : UInt64)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start amount)
    (tag : output.tag = tracker.global.nextPointerTag)
    (post : Before) (present : Present (ActualWorld post) id (W.allocation.setExtra output.child.tree))
    (rootTag : output.global.rootTag? id = tracker.global.rootTag? id)
    (actual : ActualRealized (ActualWorld post) output.global.protectedTags)
    (distinct : output.child.tree.roots.toList.Nodup) (short : output.child.tree.nodes.size < 65536)
    (startEq : start.toNat = offset) (amountEq : amount.toNat = length)
    (bounds : start.toNat+amount.toNat ≤ output.child.tree.locations.size.bytes.toNat)
    (visit : ChildrenVisitMode) :
    let result := output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes amount)
      .Write output.global.protectedTags visit
    result.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts result.tree output.global ∧
    ParentInterpretation result.tree (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) ∧
    GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority result.tree
        (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
      start (start+amount) result.tree.locations ∧
    result.tree.nodes = output.child.tree.nodes ∧ result.tree.roots = output.child.tree.roots ∧
    result.tree.tagMapping = output.child.tree.tagMapping ∧ result.tree.locations.size = output.child.tree.locations.size := by
  let result := output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes amount)
    .Write output.global.protectedTags visit
  have contract := CurrentCallResourceChildWrite.child_write_contract W runtime output child start amount witness tag post present rootTag actual
    distinct short startEq amountEq bounds visit
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts result.tree output.global := by
    rw [contract.tree_eq]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations output.child.tree _ witness.runtime.formed.toGraphState,contract.well⟩,?_⟩,
      ?_,?_,⟨witness.runtime.below.mapping,witness.runtime.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(contract.runtime cursor valid).2.1.present,(contract.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid
      exact (contract.runtime cursor valid).1
    · intro cursor valid
      exact (contract.runtime cursor valid).2.2
  have parents : ParentInterpretation result.tree
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) := by
    rw [contract.tree_eq]
    refine ⟨GeneralBorrowStructuralHistoryState.graph_locations output.child.tree _ witness.parents.graph,
      witness.parents.order,witness.parents.dimension,witness.parents.physical,witness.parents.edgeLive,witness.parents.primaryNone,?_⟩
    intro position root slot origin edge
    obtain ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,path⟩ := witness.parents.virtual position root slot origin edge
    exact ⟨earlier,originRoot,rootNode,originNode,before,rootSlot,rootAt,originAt,exposed,older,
      GeneralBorrowPrimaryWitnessVisibility.path_nodes (before := {output.child.tree with locations := result.tree.locations})
        (after := output.child.tree) rfl path⟩
  refine ⟨contract.completed,afterRuntime,parents,?_,contract.nodes,contract.roots,contract.tags,contract.capacity⟩
  intro cursor valid positive start stop index node found
  exact contract.rows cursor valid positive start stop index node (by rw [←contract.nodes];exact found)

private theorem keys_apart {α β : Type} (rows : List α) (keys : α→List β)
    (unique : (rows.flatMap keys).Nodup) (first second : α)
    (firstMem : first∈rows) (secondMem : second∈rows) (different : first≠second)
    (key : β) (firstKey : key∈keys first) (secondKey : key∈keys second) : False := by
  induction rows with
  | nil => cases firstMem
  | cons head tail ih =>
    have parts := List.nodup_append.mp (show (keys head++tail.flatMap keys).Nodup from unique)
    rcases List.mem_cons.mp firstMem with sameFirst | firstTail
    · subst first
      rcases List.mem_cons.mp secondMem with sameSecond | secondTail
      · exact different sameSecond.symm
      · exact parts.2.2 key firstKey key (List.mem_flatMap.mpr ⟨second,secondTail,secondKey⟩) rfl
    · rcases List.mem_cons.mp secondMem with sameSecond | secondTail
      · subst second
        exact parts.2.2 key secondKey key (List.mem_flatMap.mpr ⟨first,firstTail,firstKey⟩) rfl
      · exact ih parts.2.1 firstTail secondTail

/-- Minimal heap facts after installing actual writeUninit storage. Its
provenance map and initialization mask are intentionally unconstrained here. -/
theorem install (before final : Before) (tracker : MachineHooks.BorrowState)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀ row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row=>row.1==id)=some (id,entry))
    (updated : Allocation Provenance BorrowTree)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra tracker.global)
    (roots : updated.extra.roots=entry.allocation.extra.roots)
    (tags : updated.extra.tagMapping=entry.allocation.extra.tagMapping)
    (tracked : final.borrowTracker=some tracker)
    (memory : final.memory.live=(before.memory.live.filter (fun row=>row.1!=id)).push
      (id,{entry with allocation:=updated})) :
    final.borrowTracker=some tracker ∧
    (final.memory.live.toList.map Prod.fst).Nodup ∧
    (final.memory.live.toList.flatMap fun row=>row.2.allocation.extra.tagMapping.mapping.toList.map Prod.fst).Nodup ∧
    (∀ row∈final.memory.live.toList,DuplicatePrefixBorrowContract.RuntimeFacts row.2.allocation.extra tracker.global) ∧
    (∀ row∈final.memory.live.toList,row.2.allocation.extra.roots.toList.Nodup) ∧
    (∀ row∈final.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
      tracker.global.protectedTags tracker.global.nextPointerTag) ∧
    ActualRealized (ActualWorld final) tracker.global.protectedTags := by
  let keys := fun row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind =>
    row.2.allocation.extra.tagMapping.mapping.toList.map Prod.fst
  let kept := before.memory.live.toList.filter (fun row=>row.1!=id)
  have originalMem : (id,entry)∈before.memory.live.toList := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)
  have rows : final.memory.live.toList=kept++[(id,{entry with allocation:=updated})] := by
    simp only [memory,Array.toList_push,Array.toList_filter,kept]
  have memberCases (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) (member : row∈final.memory.live.toList) :
      (row∈before.memory.live.toList ∧ row.1≠id) ∨ row=(id,{entry with allocation:=updated}) := by
    rw [rows,List.mem_append,List.mem_singleton] at member
    rcases member with old | same
    · exact Or.inl ⟨(List.mem_filter.mp old).1,by simpa using (List.mem_filter.mp old).2⟩
    · exact Or.inr same
  have idsKept : (kept.map Prod.fst).Nodup := by
    simpa only [List.Nodup,List.filter_map,Function.comp_def,kept] using state.allocationIds.filter (fun key=>key != id)
  have ids : (final.memory.live.toList.map Prod.fst).Nodup := by
    rw [rows,List.map_append]
    apply List.nodup_append.mpr
    refine ⟨idsKept,by simp,?_⟩
    intro key member other singleton same
    have otherEq : other=id := by simpa using singleton
    subst other
    subst key
    obtain ⟨row,rowMem,rowId⟩ := List.mem_map.mp member
    have different := (List.mem_filter.mp rowMem).2
    simp only [rowId,bne_self_eq_false,Bool.false_eq_true] at different
  have parts : (∀ row∈before.memory.live.toList,(keys row).Nodup) ∧
      List.Pairwise (fun left right=>∀ key∈keys left,∀ other∈keys right,key≠other) before.memory.live.toList :=
    List.pairwise_flatMap.mp state.tags
  have keptTags : (kept.flatMap keys).Nodup := by
    apply List.pairwise_flatMap.mpr
    exact ⟨fun row member=>parts.1 row (List.mem_filter.mp member).1,parts.2.filter _⟩
  have updatedKeys : keys (id,{entry with allocation:=updated})=keys (id,entry) := by simp only [keys,tags]
  have allTags : (final.memory.live.toList.flatMap keys).Nodup := by
    rw [rows,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,updatedKeys]
    apply List.nodup_append.mpr
    refine ⟨keptTags,parts.1 (id,entry) originalMem,?_⟩
    intro key member other otherMem same
    subst other
    obtain ⟨row,rowMem,keyMem⟩ := List.mem_flatMap.mp member
    have different : row≠(id,entry) := by
      intro equal
      have notId := (List.mem_filter.mp rowMem).2
      simp only [equal,bne_self_eq_false,Bool.false_eq_true] at notId
    exact keys_apart _ keys state.tags row (id,entry) (List.mem_filter.mp rowMem).1 originalMem different key keyMem otherMem
  have allRuntime : ∀ row∈final.memory.live.toList,DuplicatePrefixBorrowContract.RuntimeFacts row.2.allocation.extra tracker.global := by
    intro row member
    rcases memberCases row member with ⟨old,_⟩ | same
    · exact ⟨state.formed row old,state.coherent row old,state.possible row old,highwater row old⟩
    · subst row;exact runtime
  refine ⟨tracked,ids,allTags,allRuntime,?_,?_,?_⟩
  · intro row member
    rcases memberCases row member with ⟨old,_⟩ | same
    · exact state.roots row old
    · subst row;rw [roots];exact state.roots (id,entry) originalMem
  · intro row member
    exact (allRuntime row member).below
  · apply CandidateCurrentGrantRuntime.actual (ActualWorld final) tracker.global
    intro allocationId allocation present
    simp only [Present,ActualWorld,Array.toList_map] at present
    obtain ⟨row,member,same⟩ := List.mem_map.mp present
    rcases Prod.mk.inj same with ⟨rfl,rfl⟩
    exact allRuntime row member

/-- Actual Bool protection with minimal post-write resources; ONE activation is invoked. -/
theorem activate_resources (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (machine : Before) (tracker : MachineHooks.BorrowState) (data : Identities) (owner : Nat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (state : DuplicatePrefixRuntimeInput.State machine tracker)
    (highwater : ∀ row∈machine.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (W : UniformWindow machine tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=W.pointer.value) (allocation : physical.entry.allocation=W.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (short : W.allocation.extra.nodes.size+1<65536)
    (ghost : machine.user.payload.ghost=false) (race : machine.dataRace=none) (backend : machine.user.payload.payload.user.backend=.none)
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1) :
    ∃ (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex),
      CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame physical.id W.pointer.value.provenance physical.offset 1=.ok output ∧
      output.tag=tracker.global.nextPointerTag ∧ output.global=(registered tracker.global borrowFrame physical.id fresh).1 ∧
      output.frame=(registered tracker.global borrowFrame physical.id fresh).2 ∧
      Nonempty (CurrentCallResourceFnEntry.BorrowWitness W output child physical.offset 1) ∧
    let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
    let written := output.child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
    ∃ updated, (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames frame machine)=
      .ok () {retagged with machine:={retagged.machine with memory:={retagged.machine.memory with live:=
        ((retagged.machine.memory.live.filter (fun row=>row.1 != physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}} ∧
      updated.extra=written.tree ∧ updated.byteSize=physical.entry.allocation.byteSize ∧ updated.len=physical.entry.allocation.len ∧
      updated.mutability=.Mut ∧ Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        ((physical.entry.allocation.setExtra output.child.tree).setExtra written.tree)=.ok () updated ∧
      AllocationCopy.snapshot updated=AllocationCopy.snapshot physical.entry.allocation ∧
      retagged.machine.borrowTracker=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).extra.borrowTracker=
        some (borrowFrame.addProtector physical.id tracker.global.nextPointerTag) ∧
      (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag).returnPlace=frame.returnPlace ∧
      DuplicatePrefixBorrowContract.RuntimeFacts updated.extra output.global ∧
      ParentInterpretation updated.extra (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) ∧
      GeneralRangeMapOrigins.OwnedOn
        (S05CompletedAncestryReadMutable.Authority updated.extra
          (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
        physical.offset (physical.offset+1) updated.extra.locations ∧
      updated.extra.nodes=output.child.tree.nodes ∧ updated.extra.roots=output.child.tree.roots ∧
      updated.extra.tagMapping=output.child.tree.tagMapping ∧ updated.extra.locations.size=output.child.tree.locations.size ∧
      let finalMachine : Before := {retagged.machine with memory := {retagged.machine.memory with live :=
        ((retagged.machine.memory.live.filter (fun row=>row.1 != physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}
      finalMachine.borrowTracker=some ⟨output.global,tracker.retagMode⟩ ∧
      (finalMachine.memory.live.toList.map Prod.fst).Nodup ∧
      (finalMachine.memory.live.toList.flatMap fun row=>row.2.allocation.extra.tagMapping.mapping.toList.map Prod.fst).Nodup ∧
      (∀ row∈finalMachine.memory.live.toList,DuplicatePrefixBorrowContract.RuntimeFacts row.2.allocation.extra output.global) ∧
      (∀ row∈finalMachine.memory.live.toList,row.2.allocation.extra.roots.toList.Nodup) ∧
      (∀ row∈finalMachine.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra
        output.global.protectedTags output.global.nextPointerTag) ∧
      ActualRealized (ActualWorld finalMachine) output.global.protectedTags := by
  obtain ⟨output,child,actual,tag,global,frameEq,⟨witness⟩,updated,protection,extra,bytes,length,mutable,
    mutation,snapshot,tracked,frameTracked,returnPlace⟩ :=
    CurrentCallResourceBoolActivation.activate options limits remaining span ctx machine tracker data owner frames frame borrowFrame
      state highwater frameBorrow place physical W pointer allocation runtime binding fresh short ghost race backend ready
  have member := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some physical.live)
  have distinct : W.allocation.extra.roots.toList.Nodup := by rw [←allocation];exact state.roots (physical.id,physical.entry) member
  have bounds : physical.offset.toNat+1≤W.allocation.extra.locations.size.bytes.toNat := by
    have length := state.treeLength (physical.id,physical.entry) member
    rw [allocation] at length
    rw [length,←allocation,physical.size]
    exact physical.bounds
  have nodeRoom : W.allocation.extra.nodes.size+1≤4294967295 := by omega
  have oldShort : W.allocation.extra.nodes.size<65536 := by omega
  have keys := CurrentCallResourceSourceKeyOrigin.operation W runtime state highwater borrowFrame fresh (by rfl) distinct oldShort nodeRoom
    physical.offset 1 rfl rfl (by decide) bounds output actual
  have afterDistinct := CurrentCallResourceSourceKeyOrigin.roots W runtime state highwater borrowFrame fresh (by rfl) distinct oldShort nodeRoom
    physical.offset 1 rfl rfl (by decide) bounds output actual
  let retagged := borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
  let next : MachineHooks.BorrowState := ⟨output.global,tracker.retagMode⟩
  have enabled : retagged.machine.borrowTracker=some next := by
    change retagged.machine.borrowTracker=some ⟨output.global,tracker.retagMode⟩
    rw [global]
    rfl
  have capacity : output.child.tree.locations.size=physical.entry.allocation.extra.locations.size := by rw [allocation];exact witness.capacity
  have keyOrigin : ∀ key index,(key,index)∈output.child.tree.tagMapping.mapping → key=tracker.global.nextPointerTag ∨∃old,(key,old)∈physical.entry.allocation.extra.tagMapping.mapping := by
    rw [allocation];exact keys
  obtain ⟨postState,postHighwater⟩ := CurrentCallSourceInstallState.install machine retagged.machine tracker next state highwater physical.id physical.entry physical.live
    borrowFrame fresh global output.child.tree witness.runtime afterDistinct capacity keyOrigin enabled rfl
  have present : Present (ActualWorld retagged.machine) physical.id (W.allocation.setExtra output.child.tree) := by
    simp only [Present,ActualWorld,Array.toList_map]
    apply List.mem_map.mpr
    refine ⟨(physical.id,{physical.entry with allocation:=physical.entry.allocation.setExtra output.child.tree}),?_,?_⟩
    · exact Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some (MemoryCopyBridge.live_lookup_replaced machine.memory physical.id _))
    · simp only [allocation]
  have rootTag : output.global.rootTag? physical.id=tracker.global.rootTag? physical.id := by rw [global];rfl
  have actualRealized := CandidateCurrentGrantRuntime.actual_state retagged.machine next postState
  have growth : output.child.tree.nodes.size≤W.allocation.extra.nodes.size+1 := by
    have literalEq : output=CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global borrowFrame physical.id fresh W.pointer.value.provenance physical.offset 1 := by
      exact Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ fresh _ _ _))
    obtain ⟨_,held,_,_,_,freshTag⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare W.allocation.extra tracker.global borrowFrame physical.id fresh runtime
    let registration := registered tracker.global borrowFrame physical.id fresh
    let accessed := output.access
    obtain ⟨_,afterRuntime,_,_,nodes,_,tags,bytes⟩ := CurrentCallResourceFnEntry.prepare_read W runtime state highwater borrowFrame fresh (by rfl)
      distinct oldShort physical.offset 1 rfl rfl bounds
    change DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global borrowFrame physical.id fresh W.pointer.value.provenance physical.offset 1).access.tree registration.1 at afterRuntime
    rw [←literalEq] at afterRuntime
    change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global borrowFrame physical.id fresh W.pointer.value.provenance physical.offset 1).access.tree.nodes=W.allocation.extra.nodes at nodes
    change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global borrowFrame physical.id fresh W.pointer.value.provenance physical.offset 1).access.tree.tagMapping=W.allocation.extra.tagMapping at tags
    change (CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global borrowFrame physical.id fresh W.pointer.value.provenance physical.offset 1).access.tree.locations.size=W.allocation.extra.locations.size at bytes
    rw [←literalEq] at nodes tags bytes
    have freshAfter : GeneralBorrowTagMap.Fresh output.access.tree.tagMapping tracker.global.nextPointerTag := by rw [tags];exact freshTag
    have room : output.access.tree.nodes.size+1≤4294967295 := by rw [nodes];exact nodeRoom
    have childBounds : physical.offset.toNat+1≤output.access.tree.locations.size.bytes.toNat := by rw [bytes];exact bounds
    have tagBound : tracker.global.nextPointerTag.value.toNat<registration.1.nextPointerTag.value.toNat := by
      have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
      change tracker.global.nextPointerTag.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
      omega
    have tagHeld : registration.1.protectedTags.contains tracker.global.nextPointerTag=true := by unfold ProtectedTags.contains;rw [held];rfl
    have childEq : output.child=output.access.tree.newChild (Size.ofBytes physical.offset) (CandidateCurrentWindowPointerChecks.extraOf W.pointer.value.provenance)
      tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true := by rw [literalEq];rfl
    cases prov : W.pointer.value.provenance with
    | concrete id parentTag =>
      obtain ⟨parentNode,parentAt,_,binds⟩ := W.binding
      rw [prov] at binds
      have parentAfter : output.access.tree.nodeAt W.pointer.grant=some parentNode := by change output.access.tree.nodes.get _=_;rw [nodes];exact parentAt
      have tagged : output.access.tree.indexOfTag parentTag=some W.pointer.grant := by rw [binds.2];exact afterRuntime.formed.allocator.nodeTags _ _ parentAfter
      have ctor := GeneralBorrowProtectedConstructorRuntime.construct output.access.tree registration.1 afterRuntime parentTag tracker.global.nextPointerTag W.pointer.grant parentNode
        tagged parentAfter freshAfter room tagBound tagHeld physical.offset 1 (by decide) childBounds
      rw [childEq]
      simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf,nodes] using ctor.2.2.2
    | wildcard =>
      have ctor := GeneralBorrowWildcardConstructorRuntime.protected_mutable output.access.tree registration.1 afterRuntime tracker.global.nextPointerTag freshAfter room tagBound tagHeld
        physical.offset 1 (by decide) childBounds
      rw [childEq]
      simpa only [prov,CandidateCurrentWindowPointerChecks.extraOf,nodes] using ctor.2.2.2.1
  have afterShort : output.child.tree.nodes.size<65536 := by omega
  have afterBounds : physical.offset.toNat+1≤output.child.tree.locations.size.bytes.toNat := by rw [witness.capacity];exact bounds
  obtain ⟨writeDone,writeRuntime,writeParents,writeOwned,writeNodes,writeRoots,writeTags,writeCapacity⟩ :=
    child_write_runtime W runtime output child physical.offset 1 witness tag retagged.machine present rootTag actualRealized
      afterDistinct afterShort rfl rfl afterBounds .VisitChildrenOfAccessed
  have updatedExtra : updated.extra = (output.child.tree.performBorrowAccessRange (.concrete output.tag)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed).tree := by
    rw [tag,global]
    exact extra
  have updatedRuntime : DuplicatePrefixBorrowContract.RuntimeFacts updated.extra output.global := by rw [updatedExtra];exact writeRuntime
  have updatedParents : ParentInterpretation updated.extra
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) := by rw [updatedExtra];exact writeParents
  have updatedOwned : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority updated.extra
        (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) output.global.protectedTags child)
      physical.offset (physical.offset+1) updated.extra.locations := by rw [updatedExtra];exact writeOwned
  have updatedNodes : updated.extra.nodes=output.child.tree.nodes := by rw [updatedExtra];exact writeNodes
  have updatedRoots : updated.extra.roots=output.child.tree.roots := by rw [updatedExtra];exact writeRoots
  have updatedTags : updated.extra.tagMapping=output.child.tree.tagMapping := by rw [updatedExtra];exact writeTags
  have updatedCapacity : updated.extra.locations.size=output.child.tree.locations.size := by rw [updatedExtra];exact writeCapacity
  let finalMachine : Before := {retagged.machine with memory := {retagged.machine.memory with live :=
    ((retagged.machine.memory.live.filter (fun row=>row.1 != physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}
  let entryBefore : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    {physical.entry with allocation:=physical.entry.allocation.setExtra output.child.tree}
  have entryLive : retagged.machine.memory.live.find? (fun row=>row.1==physical.id)=some (physical.id,entryBefore) :=
    MemoryCopyBridge.live_lookup_replaced machine.memory physical.id _
  have minimal := install retagged.machine finalMachine next postState postHighwater physical.id entryBefore entryLive updated
    updatedRuntime updatedRoots updatedTags enabled rfl
  exact ⟨output,child,actual,tag,global,frameEq,⟨witness⟩,updated,protection,extra,bytes,length,mutable,mutation,snapshot,
    tracked,frameTracked,returnPlace,updatedRuntime,updatedParents,updatedOwned,updatedNodes,updatedRoots,updatedTags,updatedCapacity,minimal⟩


end
end DuplicatePrefix.CurrentCallBoolWriteRuntime
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallBoolWriteRuntime" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved Bool write runtime dependency {dependency}"
