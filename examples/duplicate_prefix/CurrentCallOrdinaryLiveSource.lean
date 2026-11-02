import duplicate_prefix.CurrentCallOrdinaryInput
import duplicate_prefix.CurrentCallFamilySpatialAdmission
import duplicate_prefix.CurrentCallSpatialSourceCheckpoint
import duplicate_prefix.CurrentCallPreparedResources
import duplicate_prefix.CurrentCallSpatialEntryControl

namespace DuplicatePrefix.CurrentCallOrdinaryLiveSource
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallOrdinaryInput CurrentCallFamilySatisfaction
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

open Lean Elab Tactic in
elab "live_source_rule " suffix:str : term => do
  let found := (←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with | [(name,_)]=>return mkConst name | _=>throwError "expected checked source rule {suffix.getString}"

/-- A live source is extracted without a return allocation or return witness. -/
theorem extract {before tracker} (family : Family) (offset len capacity : UInt64)
    (live : LiveRole before tracker family offset len capacity true)
    (selected : SelectedPointer before tracker family offset capacity)
    (runtime : ∀entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,entry) →
      DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (order : ∀entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,entry) →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra)
    (distinct : ∀entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,entry) →entry.allocation.extra.roots.toList.Nodup) :
    ∃(context : Context before)(role : RoleCover before tracker context .mut offset.toNat len.toNat)
      (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind),
      role.family=family ∧role.backing.allocation=entry.allocation ∧
      before.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,entry) ∧
      CandidateCallBindings.WindowBinding before family.value family.allocation offset.toNat len.toNat ∧
      Physical entry.allocation offset len true := by
  obtain ⟨entry,found,size,physical,cap,owned⟩:=live
  have points:=CurrentCallPointwiseSpatialCover.pointwise_of_chains cap (runtime entry found) (order entry found) (distinct entry found) (to_chained owned)
  let backing : AllocationCover before := (live_source_rule ".CurrentCallPointwiseSpatialCover.backing") cap.live points
  let context : Context before := ⟨#[backing],by simp [backing]⟩
  have bound : offset.toNat+len.toNat≤entry.allocation.len := by rw [physical.1.1];exact physical.2.2.1
  let role : RoleCover before tracker context .mut offset.toNat len.toNat :=
    (live_source_rule ".CurrentCallPointwiseSpatialCover.role") cap.live points bound context (by change backing∈([backing] : List (AllocationCover before));simp)
  obtain ⟨base,cached,room,address,nonnull,represented⟩:=selected
  have bytes : entry.allocation.len=capacity.toNat := by rw [physical.1.1,size];rfl
  have binding : CandidateCallBindings.WindowBinding before family.value family.allocation offset.toNat len.toNat := by
    refine ⟨entry,base,found,cached,physical.1.1,?_,bound,address,nonnull,?_⟩
    · rw [bytes];exact room
    · cases provenance : family.value.provenance with
      | concrete id tag=>rw [provenance] at represented;exact represented.1
      | wildcard=>rw [provenance] at represented;simpa only [size] using represented
  exact ⟨context,role,entry,rfl,rfl,found,binding,physical⟩

private theorem fresh {options limits remaining span before argument length place}
    (input : OrdinaryInput options limits remaining span before argument length place) :
    input.tracker.global.nextPointerTag.value<18446744073709551615 := by
  have room:=input.resources.tagRoom
  simpa [UInt64.lt_iff_toNat_lt] using (show input.tracker.global.nextPointerTag.value.toNat<18446744073709551615 by omega)

/-- The actual source copy needs no live Bool allocation. -/
theorem copy {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (family : Family) (offset capacity : UInt64)
    (positive : 0<len.toNat) (fits : len.toNat<9223372036854775808)
    (encoding : argument=.pointer family.value) (assigned : input.assignment.Binds input.sourceOccurrence family)
    (charge : CurrentCallPointwiseSpatialCover.ExactCharge input.Fs input.sourceOwner .mut family.allocation offset.toNat len.toNat)
    (selected : SelectedPointer before input.tracker family offset capacity)
    (liveRole : LiveRole before input.tracker family offset len capacity true)
    (sourceReady : (∃entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,entry)) →
      CurrentCallBoolProtection.WindowReady before family.allocation offset.toNat len.toNat) :
    let machine:=CurrentCallPush.preparedMachine before #[]
    let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
    let first:=(firstLive root).frame
    ∃context : Context machine,∃role : RoleCover machine input.tracker context .mut offset.toNat len.toNat,
    ∃(entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)(doneFrame : CompilerFrameContext.ActualFrame),
    let output:=CurrentCallSpatialEntryRead.output role {} (fresh input) (UInt64.ofNat offset.toNat) len
    ∃source : CurrentCallPostEntryCheckpoint.Source
      (CurrentCallSpatialSourceInstall.copiedMachine role {} (fresh input) (UInt64.ofNat offset.toNat) len entry)
      ⟨output.global,input.tracker.retagMode⟩ offset.toNat len,
      role.family=family ∧CurrentCallPostEntryCheckpoint.CopyReady source ∧
      input.assignment.Binds input.sourceOccurrence role.family ∧
      MachineHooks.withRetagMode .FnEntry
        ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
          ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span family.value len).imm,ActualReferenceMetadata.reference⟩
          (LocalPlaces.localRuntimePlace 0 first 1 ActualReferenceMetadata.reference).stackView)
        (Storage.withCurrent #[] first machine)=.ok () (Storage.withCurrent #[] doneFrame
          (CurrentCallSpatialSourceInstall.copiedMachine role {} (fresh input) (UInt64.ofNat offset.toNat) len entry)) ∧
      before.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,entry) ∧
      entry.allocation=role.backing.allocation ∧
      source.role.family=CurrentCallSpatialSourceInstall.childFamily role output.tag ∧
      source.tag=input.tracker.global.nextPointerTag ∧
      source.role.backing.allocation=role.backing.allocation.setExtra output.child.tree ∧
      doneFrame.extra.borrowTracker=some output.frame ∧
      source.node.children=#[] ∧source.role.backing.allocation.extra.nodes.size+7<65536 ∧
      output.global.nextPointerTag.value.toNat=input.tracker.global.nextPointerTag.value.toNat+1 ∧
      doneFrame=(CurrentCallSourceArguments.doneRoot options remaining span root {} family.value len family.allocation input.tracker.global.nextPointerTag).frame ∧
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span family.value len).imm,ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace 0 first 1 ActualReferenceMetadata.reference).stackView
        (Storage.withCurrent #[] first (ScopedFrame.entered machine input.tracker .FnEntry))=
        .ok () (Storage.withCurrent #[] doneFrame
          (CurrentCallTypedSourceCopy.validated machine input.tracker (fresh input) role.backing.id entry output.child.tree)) := by
  dsimp only
  let machine:=CurrentCallPush.preparedMachine before #[]
  let root:=CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let first:=(firstLive root).frame
  have preparedRole : LiveRole machine input.tracker family offset len capacity true := by
    obtain ⟨entry,live,size,physical,cap,owned⟩:=liveRole
    exact ⟨entry,live,size,physical,⟨cap.live,cap.extent,cap.treeExtent,cap.rootSlot,cap.rootNode⟩,owned⟩
  have selectedPrepared : SelectedPointer machine input.tracker family offset capacity := selected
  have runtimeSelected : ∀entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      machine.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,entry) →
      DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra input.tracker.global := by
    intro entry live
    have member:=Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)
    exact ⟨input.runtime.formed _ member,input.runtime.coherent _ member,input.runtime.possible _ member,input.resources.tagsBelow _ member⟩
  obtain ⟨context,role,originalEntry,familyEq,allocationEq,originalLive,binding,physical⟩:=extract family offset len capacity preparedRole selectedPrepared
    runtimeSelected (fun entry live=>input.runtime.parent_order _ _ live)
    (fun entry live=>input.runtime.roots _ (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live)))
  have roleId : role.backing.id=family.allocation:=role.id.symm.trans (congrArg Family.allocation familyEq)
  have member:=Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some originalLive)
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra input.tracker.global := by
    rw [allocationEq];exact runtimeSelected originalEntry originalLive
  have distinct : role.backing.allocation.extra.roots.toList.Nodup := by
    rw [allocationEq];exact input.runtime.roots _ member
  have room : role.backing.allocation.extra.nodes.size+8<65536 := by
    rw [allocationEq];have oldRoom : originalEntry.allocation.extra.nodes.size+16<65536:=input.resources.nodeRoom _ member;omega
  have sourcePhysical : OrdinaryPhysicalValidity.MutU8Slice role.backing.allocation (UInt64.ofNat offset.toNat) len := by
    rw [allocationEq,UInt64.ofNat_toNat]
    obtain ⟨⟨storage,maskValid,maskLength,provenance⟩,mutable,bounds,initialized⟩:=physical
    exact ⟨⟨storage,maskLength,maskValid,provenance⟩,positive,fits,bounds,mutable,initialized rfl⟩
  have storage : CurrentCallResourceEntrySourceStorage.Data role.backing.allocation (UInt64.ofNat offset.toNat) len :=
    (live_source_rule ".CurrentCallResourceEntrySourceStorage.initial") sourcePhysical
      (by rw [allocationEq];exact input.resources.storageRoom _ member)
  have profile : CurrentCallBoolProtection.WindowReady machine role.backing.id offset.toNat len.toNat := by
    rw [roleId];exact sourceReady ⟨originalEntry,originalLive⟩
  have roleBinding : CandidateCallBindings.WindowBinding machine role.family.value role.backing.id offset.toNat len.toNat := by
    simpa only [familyEq,roleId] using binding
  have frameBorrow : first.extra.borrowTracker=some ({} : FrameState) := by
    change root.frame.extra.borrowTracker=some ({} : FrameState)
    exact RootEntryFrame.raw_borrow _ _ _ input.tracker input.runtime.enabled
  have localLive : (first.locals[1]'((firstLive root).valid i1)).value=.live (.immediate .uninit) := by
    simp only [first,firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  have localCached : (first.locals[1]'((firstLive root).valid i1)).layout=some ActualReferenceMetadata.reference := by
    simp only [first,firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,firstCache,RootFrameData.cache,
      LocalOperands.cachedLayoutFrame,atSpan,i1]
  have dynamicPositive : 0<options.place.dynamicFuel := by
    have room:=input.resources.dynamicFuel;unfold DuplicatePrefixCallSpecification.work at room;omega
  have validationPositive : 0<options.limits.validation := by
    have room:=input.resources.configuredFuel.2.2.2;unfold DuplicatePrefixCallSpecification.work at room;omega
  obtain ⟨ctx,actualPointers⟩:=GlobalEmptyReferenceContext.exists_context options remaining span input.model.preciseOff input.model.implicitOff
  obtain ⟨entry,doneFrame,source,ready,copy,live,alloc,family,tag,sourceAlloc,borrowed,state⟩:=
    CurrentCallSpatialSourceCheckpoint.invoke options limits remaining span ctx machine input.tracker context offset.toNat len role runtime
      (CurrentCallPreparedResources.state input.runtime.toState #[]) input.resources.tagsBelow distinct (by omega)
      #[] first {} frameBorrow roleBinding positive fits (fresh input) input.model.noDataRace input.model.nullComparator
      (options.place.dynamicFuel-1) (options.limits.validation-1) (by omega) (by omega)
      input.model.metadata input.cacheOrigins input.model.debugOff input.model.ghostOff input.model.shallow
      1 ((firstLive root).valid i1) .uninit localLive localCached (firstLive root).noClocks storage profile
  let output:=CurrentCallSpatialEntryRead.output role {} (fresh input) (UInt64.ofNat offset.toNat) len
  have amountNonzero : len≠0 := by intro eq;rw [eq] at positive;contradiction
  have bounds : (UInt64.ofNat offset.toNat).toNat+len.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat := by
    rw [UInt64.ofNat_toNat,allocationEq,input.runtime.treeLength _ member]
    exact physical.2.2.1
  have nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295 := by omega
  obtain ⟨afterRuntime,_,child,node,lookup,nodeAt,nodeTag,nodeLeaf,nodeHidden,active⟩:=
    (live_source_rule ".CurrentCallSpatialEntryActivity.spatial_facets") role runtime {} (fresh input) rfl distinct (by omega)
      nodeRoom (UInt64.ofNat offset.toNat) len (by rw [UInt64.ofNat_toNat]) rfl amountNonzero bounds
  have sourceAt : output.child.tree.nodes.get source.grant=some source.node := by
    have atNode:=source.nodeAt
    rw [sourceAlloc] at atNode
    exact atNode
  have sourceLookup : output.child.tree.indexOfTag input.tracker.global.nextPointerTag=some source.grant := by
    rw [←tag,←source.nodeTag]
    exact afterRuntime.formed.allocator.nodeTags _ _ sourceAt
  have sameChild : source.grant=child:=Option.some.inj (sourceLookup.symm.trans lookup)
  change output.child.tree.nodes.get child=some node at nodeAt
  have sameNode : source.node=node := by rw [sameChild,nodeAt] at sourceAt;exact Option.some.inj sourceAt.symm
  have leaf : source.node.children=#[]:=by rw [sameNode];exact nodeLeaf
  have growth := (CurrentCallSpatialEntryConstructor.invoke role rfl runtime distinct (by omega) nodeRoom {} (fresh input)
    (UInt64.ofNat offset.toNat) len (by rw [UInt64.ofNat_toNat]) rfl amountNonzero bounds).2.2.2.2.2.1
  have currentRoom : source.role.backing.allocation.extra.nodes.size+7<65536 := by
    rw [sourceAlloc]
    change output.child.tree.nodes.size≤role.backing.allocation.extra.nodes.size+1 at growth
    change output.child.tree.nodes.size+7<65536
    omega
  have successor : output.global.nextPointerTag.value.toNat=input.tracker.global.nextPointerTag.value.toNat+1 := by
    change (TypedRetagEmpty.successorTag input.tracker.global.nextPointerTag (fresh input)).value.toNat=_
    have margin:=input.resources.tagRoom
    change (input.tracker.global.nextPointerTag.value+1).toNat=_
    rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt (by omega)]
  have worldIds : ((ActualWorld machine).toList.map Prod.fst).Nodup := by
    simpa only [ActualWorld,Array.toList_map,List.map_map,Function.comp_def] using (CurrentCallPreparedResources.state input.runtime.toState #[]).allocationIds
  obtain ⟨otherEntry,otherChild,otherLive,otherAllocation,actualOp,actualTag,actualGlobal,actualFrame,actualLookup,readDone,childDone,
      actualRuntime,actualCapacity,actualGrowth,actualRoots,actualOld,actualNode,typed,bundle,actualCells⟩ :=
    CurrentCallSpatialTypedSourceCopy.invoke options limits remaining span ctx machine input.tracker context offset.toNat len role runtime
      worldIds distinct (by omega) nodeRoom #[] first {} input.runtime.enabled frameBorrow roleBinding positive fits (fresh input)
      input.model.noDataRace input.model.nullComparator (options.place.dynamicFuel-1) (options.limits.validation-1) (by omega) (by omega)
      input.model.metadata input.cacheOrigins input.model.debugOff input.model.ghostOff input.model.shallow
      1 ((firstLive root).valid i1) .uninit localLive localCached (firstLive root).noClocks
  have equalEntry : otherEntry=entry := (Prod.mk.inj (Option.some.inj (otherLive.symm.trans live))).2
  subst otherEntry
  let expected:=CurrentCallSourceArguments.doneRoot options remaining span root {} role.family.value len role.backing.id input.tracker.global.nextPointerTag
  have exactScoped := bundle.2.2.1
  have stateEq := (EStateM.Result.ok.inj (copy.symm.trans exactScoped)).2
  have frameEq : doneFrame=expected.frame := by
    have atFrame:=congrArg (fun result : RootState=>result.stack.frames[0]?) stateEq
    change some doneFrame=some expected.frame at atFrame
    exact Option.some.inj atFrame
  have exactUnscoped := bundle.2.1
  refine ⟨context,role,entry,doneFrame,source,familyEq,ready,?_,?_,?_,alloc,family,tag,sourceAlloc,borrowed,leaf,currentRoom,successor,?_,?_⟩
  · simpa only [familyEq] using assigned
  · simpa only [first,machine,root,familyEq,Array.size_empty] using copy
  · simpa only [roleId,machine,CurrentCallPush.preparedMachine,CallEntryFacts.cacheTop,CallEntryFacts.freshRoot] using live
  · simpa only [expected,roleId,familyEq,root] using frameEq
  · rw [frameEq]
    simpa only [first,machine,root,familyEq,Array.size_empty,expected,CurrentCallSourceArguments.doneRoot] using exactUnscoped

end
end DuplicatePrefix.CurrentCallOrdinaryLiveSource

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallOrdinaryLiveSource" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved source-only live-copy dependency {dependency}"
