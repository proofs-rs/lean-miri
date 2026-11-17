import duplicate_prefix.CurrentCallEntry
import duplicate_prefix.GeneralBorrowRawSharedExpression
import duplicate_prefix.S05ConcreteFnEntryRaw
import duplicate_prefix.GeneralBorrowSharedConstructorRuntime

namespace DuplicatePrefix.CurrentCallSharedReference
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo RootReferenceTrees
open GeneralBorrowRawSharedExpression
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The installed source tree follows actual allocation identity. -/
def sourceTree {before tracker frame argument len place call data}
    {raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data}
    (borrowed : CurrentCallBoolProtection.Borrowed raw) : BorrowTree :=
  if call.sourceId = call.returnId then (CurrentCallBoolProtection.writeResult borrowed).tree else raw.output.child.tree

def sourceCompletion {before tracker frame argument len place call data}
    {raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data}
    (borrowed : CurrentCallBoolProtection.Borrowed raw) : CandidateStableCallOwnership.Completion :=
  if call.sourceId = call.returnId then
    S05ConcreteProtectedChildCompletion.extend (CurrentCallBoolProtection.returnCompletion raw) borrowed.child raw.returnPointer.grant
  else S05ConcreteProtectedChildCompletion.extend raw.sourcePrecise.completion raw.child raw.sourcePointer.grant

/-- The source child is an actual stored node. Bool construction preserves
this exact old node's tag, including when both roles share the allocation. -/
theorem source_node {before tracker frame argument len place call data}
    (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (borrowed : CurrentCallBoolProtection.Borrowed raw) (written : CurrentCallBoolProtection.Written borrowed) :
    ∃ node, (sourceTree borrowed).nodes.get raw.child = some node ∧ node.tag = raw.output.tag := by
  obtain ⟨node,present,tag⟩ := raw.childNode
  by_cases same : call.sourceId = call.returnId
  · obtain ⟨next,found,nextTag,_,_⟩ := borrowed.metadata.old raw.child node
      (by simpa only [CurrentCallBoolProtection.returnTree,same,ite_true] using present)
    refine ⟨next,?_,nextTag.trans tag⟩
    simpa only [sourceTree,same,ite_true,written.nodes] using found
  · exact ⟨node,by simpa only [sourceTree,same,ite_false] using present,tag⟩

/-- Bool protection retains source authority on the entire buffer under the
actual installed global; the source may share its allocation with the Bool. -/
theorem source_ready {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (borrowed : CurrentCallBoolProtection.Borrowed raw) (written : CurrentCallBoolProtection.Written borrowed) :
    DuplicatePrefixBorrowContract.RuntimeFacts (sourceTree borrowed) borrowed.output.global ∧
    CandidateStableCallOwnership.Completes (sourceTree borrowed) (sourceCompletion borrowed) ∧
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder (sourceTree borrowed) ∧
    GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority (sourceTree borrowed) (sourceCompletion borrowed) borrowed.output.global.protectedTags raw.child)
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) (sourceTree borrowed).locations := by
  refine ⟨?_,?_,?_,written.sourceOwned⟩
  · by_cases same : call.sourceId = call.returnId
    · simpa only [sourceTree,same,ite_true] using written.runtime
    · obtain ⟨room,_,_⟩ := CurrentCallBoolProtection.return_budget input frame raw
      have outputEq : borrowed.output = CurrentCallTypedFnEntry.literal (CurrentCallBoolProtection.returnTree raw)
          raw.output.global raw.output.frame call.returnId room raw.returnPointer.value.provenance
          (UInt64.ofNat call.returnOffset) 1 := Except.ok.inj (borrowed.actual.symm.trans
            (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
      have globalEq : borrowed.output.global = (GeneralBorrowFnEntryRegistration.registered
          raw.output.global raw.output.frame call.returnId room).1 := by rw [outputEq];rfl
      obtain ⟨_,_,_,current,_,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare raw.output.child.tree raw.output.global
        raw.output.frame call.returnId room raw.runtime
      simpa only [sourceTree,same,ite_false,globalEq] using current
  · by_cases same : call.sourceId = call.returnId
    · simpa only [sourceTree,sourceCompletion,same,ite_true] using written.completes
    · simpa only [sourceTree,sourceCompletion,same,ite_false] using raw.completes
  · by_cases same : call.sourceId = call.returnId
    · have ordered := GeneralBorrowParentTagInvariant.nodes_frame borrowed.output.child.tree
        (CurrentCallBoolProtection.writeResult borrowed).tree written.nodes borrowed.metadata.order
      simpa only [sourceTree,same,ite_true] using ordered
    · simpa only [sourceTree,same,ite_false] using raw.outputOrder

private theorem borrowed_global {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (borrowed : CurrentCallBoolProtection.Borrowed raw) :
    ∃ room : raw.output.global.nextPointerTag.value < 18446744073709551615,
      borrowed.output.global = (GeneralBorrowFnEntryRegistration.registered raw.output.global raw.output.frame call.returnId room).1 := by
  obtain ⟨room,_,_⟩ := CurrentCallBoolProtection.return_budget input frame raw
  have outputEq : borrowed.output = CurrentCallTypedFnEntry.literal (CurrentCallBoolProtection.returnTree raw)
      raw.output.global raw.output.frame call.returnId room raw.returnPointer.value.provenance
      (UInt64.ofNat call.returnOffset) 1 := Except.ok.inj (borrowed.actual.symm.trans
        (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  exact ⟨room,by rw [outputEq];rfl⟩

/-- Actual entry consumes two of the original finite tag/node reserves. No
resource predicate is requested on the temporary postentry machine. -/
theorem source_budget {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (borrowed : CurrentCallBoolProtection.Borrowed raw) (written : CurrentCallBoolProtection.Written borrowed) :
    borrowed.output.global.nextPointerTag.value < 18446744073709551615 ∧
    (sourceTree borrowed).nodes.size+1 ≤ 4294967295 ∧ (sourceTree borrowed).nodes.size < 65536 := by
  obtain ⟨room,globalEq⟩ := borrowed_global input frame raw borrowed
  have first : raw.output.global.nextPointerTag = TypedRetagEmpty.successorTag tracker.global.nextPointerTag raw.tagRoom := by
    rw [raw.outputGlobal];rfl
  have second : borrowed.output.global.nextPointerTag = TypedRetagEmpty.successorTag raw.output.global.nextPointerTag room := by
    rw [globalEq];rfl
  have step1 := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag raw.tagRoom
  have step2 := GenericFunctionEntryNumerics.successor_value raw.output.global.nextPointerTag room
  have reserve := input.machine.resources.tagRoom
  have tagRoom : borrowed.output.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    rw [second]
    change (TypedRetagEmpty.successorTag raw.output.global.nextPointerTag room).value.toNat < 18446744073709551615
    have firstNat := congrArg (fun tag : BorTag => tag.value.toNat) first
    omega
  have margin : raw.sourceAllocation.extra.nodes.size+16 < 65536 := by
    have present := raw.sourcePresent
    simp only [CandidateStableCallOwnership.Present,CandidateCurrentJointCall.ActualWorld,Array.toList_map] at present
    obtain ⟨⟨id,entry⟩,member,equal⟩ := List.mem_map.mp present
    have allocEq := (Prod.mk.inj equal).2
    change entry.allocation = raw.sourceAllocation at allocEq
    rw [←allocEq]
    exact input.machine.resources.nodeRoom (id,entry) member
  have growth : (sourceTree borrowed).nodes.size ≤ raw.sourceAllocation.extra.nodes.size+2 := by
    have sourceGrowth := raw.outputGrowth
    have boolGrowth := borrowed.metadata.growth
    by_cases same : call.sourceId = call.returnId
    · simp only [CurrentCallBoolProtection.returnTree,same,ite_true] at boolGrowth
      simp only [sourceTree,same,ite_true,written.nodes]
      omega
    · simp only [sourceTree,same,ite_false]
      omega
  exact ⟨tagRoom,by omega,by omega⟩

/-- Default shared reborrow certificates from current completed mutable authority.
Only the real fresh-tag allocation, associated Read, and shared constructor occur.
The caller does not supply success of any of these operations. -/
theorem raw_steps (tree : BorrowTree) (global : GlobalState)
    (completion : CandidateStableCallOwnership.Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : CandidateStableCallOwnership.Completes tree completion)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (position : Nat) (selected parent : UniIndex) (selectedNode parentNode : TreeNode)
    (slot : tree.roots[position]? = some selected)
    (selectedPresent : tree.nodes.get selected = some selectedNode)
    (parentPresent : tree.nodes.get parent = some parentNode)
    (parentPath : GeneralBorrowExposedNonleafPrimaryPath.Path tree selected parent)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size < 65536)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority tree completion global.protectedTags parent)
      offset (offset+len) tree.locations) :
    let advanced := GeneralBorrowFnEntryRegistration.advanced global room
    (read tree advanced.protectedTags parentNode.tag offset len .VisitChildrenOfAccessed).status = .Completed ∧
    (child tree advanced.protectedTags parentNode.tag global.nextPointerTag offset len .VisitChildrenOfAccessed).outcome = .ok () := by
  let advanced := GeneralBorrowFnEntryRegistration.advanced global room
  have high := GeneralBorrowForestTagHighWater.complete tree _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨fresh,_,unheld⟩ := GenericFunctionTagFormation.fresh_above tree _ _ global.nextPointerTag high (Nat.le_refl _)
  obtain ⟨allocated,actual,below⟩ := GeneralBorrowForestTagHighWaterHistory.allocate tree global room runtime.below runtime.formed.allocator.nodeTags false
  have equal : advanced = allocated := congrArg Prod.fst
    (Except.ok.inj ((TypedRetagEmpty.allocate_tag global room).symm.trans actual))
  rw [←equal] at below
  have current : DuplicatePrefixBorrowContract.RuntimeFacts tree advanced :=
    ⟨runtime.formed,runtime.coherent,runtime.possible,by
      simpa only [GeneralBorrowFreshSharedSequence.registered,Bool.false_eq_true,ite_false,advanced,GeneralBorrowFnEntryRegistration.advanced] using below⟩
  obtain ⟨depth⟩ := current.formed.depth
  have rows : GeneralRangeMapOrigins.OwnedOn (fun location =>
      GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location ∧
      S05CompletedAncestryReadMutable.Authority tree completion advanced.protectedTags parent location)
      offset (offset+len) tree.locations := by
    intro cursor valid positive start stop
    exact ⟨current.possible cursor valid,owned cursor valid positive start stop⟩
  have accessed := S05CompletedAncestryReadMutable.range tree completion advanced.protectedTags complete
    current.formed.toGraphState depth order position selected parent selectedNode parentNode slot selectedPresent parentPresent parentPath
    (Size.ofBytes offset) (Size.ofBytes len) offset (offset+len) rows current.formed.well
    (fun cursor valid => ⟨current.coherent cursor valid,current.formed.profile cursor valid,current.possible cursor valid⟩)
    bounds (Nat.le_refl _) (Nat.le_refl _) short .VisitChildrenOfAccessed
  let after := read tree advanced.protectedTags parentNode.tag offset len .VisitChildrenOfAccessed
  have same : after.tree = {tree with locations := after.tree.locations} := accessed.tree_eq
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts after.tree advanced := by
    rw [same]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations tree _ current.formed.toGraphState,accessed.well⟩,?_⟩,
      ?_,?_,⟨current.below.mapping,current.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(accessed.runtime cursor valid).2.1.present,(accessed.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid; exact (accessed.runtime cursor valid).1
    · intro cursor valid; exact (accessed.runtime cursor valid).2.2
  have tagged : after.tree.indexOfTag parentNode.tag = some parent := by
    unfold BorrowTree.indexOfTag
    change (tree.performBorrowAccessRange (.concrete parentNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read advanced.protectedTags .VisitChildrenOfAccessed).tree.tagMapping.get parentNode.tag = _
    rw [accessed.tags]
    exact (complete.2.2.2.2.1 parent parentNode parentPresent).1
  have present : after.tree.nodeAt parent = some parentNode := by
    change after.tree.nodes.get parent = some parentNode
    simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.nodes] using parentPresent
  have freshAfter : GeneralBorrowTagMap.Fresh after.tree.tagMapping global.nextPointerTag := by
    simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.tags] using fresh
  have tagBound : global.nextPointerTag.value.toNat < advanced.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  have constructed := GeneralBorrowSharedConstructorRuntime.construct after.tree advanced afterRuntime parentNode.tag
    global.nextPointerTag parent parentNode tagged present freshAfter (by simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.nodes] using nodeRoom)
    tagBound false unheld offset len nonzero (by simpa only [after,GeneralBorrowRawSharedExpression.read,accessed.capacity] using bounds)
  exact ⟨accessed.completed,constructed.1⟩

/-- Entry's installed source tree retains the original physical capacity. -/
theorem source_capacity {before tracker frame argument len place call data}
    (raw : CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data)
    (borrowed : CurrentCallBoolProtection.Borrowed raw) (written : CurrentCallBoolProtection.Written borrowed) :
    (sourceTree borrowed).locations.size = raw.sourceAllocation.extra.locations.size := by
  by_cases same : call.sourceId = call.returnId
  · simp only [sourceTree,same,ite_true]
    rw [written.capacity,borrowed.metadata.capacity]
    simpa only [CurrentCallBoolProtection.returnTree,same,ite_true] using raw.outputCapacity
  · simpa only [sourceTree,same,ite_false] using raw.outputCapacity

/-- Actual shared-reference rvalue composition. The current-call consumer supplies
its internally derived read and child certificates; no legacy callback authorization
is reconstructed or added to the current-call admission contract. -/
theorem rvalue_of_steps
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (region : Region)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (_defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (readCompleted : (read entry.allocation.extra tracker.global.protectedTags parentTag offset len .VisitChildrenOfAccessed).status = .Completed)
    (childCompleted : (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).outcome = .ok ())
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (different : localId ≠ 1)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : localId < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[localId].value = .live (.immediate .uninit))
    (destUncached : frame.locals[localId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler localId
      (Storage.withCurrent frames frame machine) = .ok (layout true) (Storage.withCurrent frames frame machine))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Ref region (RootReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) ⟨localId,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (ActualLocalCopy.written frame localId (layout true) validDest value.imm) resultMachine) := by
  let inner := config options remaining span
  let outer := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks outer limits
  let cachedFrame := LocalPlaces.cachePlaceLayout frame localId (layout true) validDest
  let activeTracker := {tracker with retagMode := mode true}
  let enteredMachine := RootReferenceRvalue.enter machine tracker true
  let updatedMachine := {ReferenceBorrowDriver.allocatedMachine enteredMachine activeTracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
  let value := RetagReferencePlace.sliceValue inner.access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
  let afterFrame := RootReferenceWrite.written cachedFrame localId value.imm
    (by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest)
  have info := RootReferenceInfo.facts options remaining span ctx true
  have destination := ActualLocalPlace.uncached options limits (remaining+1) span debugOff frames frame machine
    localId (layout true) validDest destUncached info.sized query
  have cachedSourceValid : (1 : MIR.LocalId) < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validSource
  have cachedDestValid : localId < cachedFrame.locals.size := by simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest
  have sourceLive' : cachedFrame.locals[1].value = .live (.immediate
      (PtrMetadataComplete.rawImmediate (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) outer.access.runtime.base len)) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,outer] using sourceLive
  have sourceCached' : cachedFrame.locals[1].layout = some ActualReferenceMetadata.reference := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,different] using sourceCached
  have sourcePlace := RootReferencePlace.actual_slice_place options limits (remaining+1) span debugOff frames cachedFrame machine
    1 (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) len cachedSourceValid sourceLive' sourceCached' noClocks ghost
  have destinationLive : cachedFrame.locals[localId].value = .live (.immediate .uninit) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using destLive
  have destinationCached : cachedFrame.locals[localId].layout = some (layout true) := by
    simp [cachedFrame,LocalPlaces.cachePlaceLayout]
  have entered : enteredMachine.borrowTracker = some activeTracker := rfl
  have current : activeTracker.retagMode = mode true := rfl
  let parentTree := (read entry.allocation.extra tracker.global.protectedTags parentTag offset len .VisitChildrenOfAccessed).tree
  let resultTree := (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
  have readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read activeTracker.global.protectedTags .VisitChildrenOfAccessed).tree = parentTree := rfl
  have readDone : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read activeTracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := readCompleted
  have child' : parentTree.newChild (Size.ofBytes offset) (.concrete parentTag) activeTracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) (initial true)) (policy true).outsidePermission false =
      ⟨resultTree,.ok ()⟩ := by
    have succeeded := childCompleted
    change (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).outcome = .ok () at succeeded
    change child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed =
      ⟨(child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree,.ok ()⟩
    cases childEq : child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed with
    | mk treeResult result =>
      simp only [childEq] at succeeded
      cases succeeded
      rfl
  have physicalBounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat := by
    rw [←capacity]
    exact bounds
  have writer := RootReferenceWrite.positive_cached options limits remaining span ctx debugOff cmp true dynamicFuel validityFuel
    fuelEq validationFuel id entry base offset len parentTag positive nonzero signedFits physicalBounds
    frames cachedFrame enteredMachine activeTracker entered current fresh localId .uninit cachedDestValid destinationLive destinationCached
    noClocks ghost shallow cachedAddress present race parentTree (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
    readTree readDone child' metadata notConstructed
  have baseEq : outer.access.runtime.base = inner.access.runtime.base := by
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,
      CanonicalConfigFacts.actual_access_runtime options () remaining span]
  have writer' : hooks.writeImmediate ()
      (PtrMetadataComplete.rawImmediate (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) outer.access.runtime.base len)
      (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout true))
      (Storage.withCurrent frames cachedFrame enteredMachine) = .ok () (Storage.withCurrent frames afterFrame updatedMachine) := by
    simpa only [hooks,outer,inner,afterFrame,value,activeTracker,baseEq,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,updatedMachine,enteredMachine,RootReferenceRvalue.enter] using writer
  have result := RootReferenceRvalue.of_write options limits (remaining+1) span true region
    (.inl (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))) len ⟨1,#[.Deref]⟩ ⟨localId,#[]⟩
    (LocalPlaces.localRuntimePlace frames.size cachedFrame localId (layout true)) (Storage.withCurrent frames frame machine)
    frames cachedFrame machine tracker (ReferenceBorrowDriver.allocatedTracker activeTracker fresh) enabled shallow rfl
    destination sourcePlace afterFrame updatedMachine rfl writer'
  simpa only [afterFrame,updatedMachine,enteredMachine,RootReferenceRvalue.enter,ReferenceBorrowDriver.allocatedMachine,
    ReferenceBorrowDriver.allocatedTracker,activeTracker,RootReferenceWrite.written,ActualLocalCopy.written,cachedFrame,value,
    inner] using result

/-- The real shared-reference expression from current authority, with the Read
and constructor certificates discharged internally. -/
theorem rvalue
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (region : Region)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (_defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (completion : CandidateStableCallOwnership.Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (complete : CandidateStableCallOwnership.Completes entry.allocation.extra completion)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra)
    (position : Nat) (selected parent : UniIndex) (selectedNode parentNode : TreeNode)
    (slot : entry.allocation.extra.roots[position]? = some selected)
    (selectedPresent : entry.allocation.extra.nodes.get selected = some selectedNode)
    (parentPresent : entry.allocation.extra.nodes.get parent = some parentNode)
    (parentPath : GeneralBorrowExposedNonleafPrimaryPath.Path entry.allocation.extra selected parent)
    (parentTagEq : parentNode.tag = parentTag)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295)
    (short : entry.allocation.extra.nodes.size < 65536)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority entry.allocation.extra completion tracker.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (different : localId ≠ 1)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : localId < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[localId].value = .live (.immediate .uninit))
    (destUncached : frame.locals[localId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler localId
      (Storage.withCurrent frames frame machine) = .ok (layout true) (Storage.withCurrent frames frame machine))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
    evalRvalueIntoPlace (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Ref region (RootReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) ⟨localId,#[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (ActualLocalCopy.written frame localId (layout true) validDest value.imm) resultMachine) := by
  have steps := raw_steps entry.allocation.extra tracker.global completion runtime complete order position selected parent
    selectedNode parentNode slot selectedPresent parentPresent parentPath fresh nodeRoom short offset len
    (by intro zero; subst len; exact (by decide : ¬ ((0 : UInt64) < 0)) positive) bounds owned
  simp only [GeneralBorrowFnEntryRegistration.advanced,parentTagEq] at steps
  exact rvalue_of_steps options limits remaining span ctx debugOff cmp region dynamicFuel validityFuel fuelEq validationFuel
    base offset len id entry positive nonzero signedFits frames frame machine tracker enabled _defaultMode fresh parentTag
    bounds steps.1 steps.2 capacity localId different validSource validDest sourceLive sourceCached destLive destUncached query
    noClocks ghost shallow cachedAddress present race metadata notConstructed

/-- Execute the next actual root MIR shared-Ref statement from current raw
authority. The Read and shared constructor are derived internally. -/
theorem statement
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (RootReferenceFacts.location true))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (completion : CandidateStableCallOwnership.Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (complete : CandidateStableCallOwnership.Completes entry.allocation.extra completion)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra)
    (position : Nat) (selected parent : UniIndex) (selectedNode parentNode : TreeNode)
    (slot : entry.allocation.extra.roots[position]? = some selected)
    (selectedPresent : entry.allocation.extra.nodes.get selected = some selectedNode)
    (parentPresent : entry.allocation.extra.nodes.get parent = some parentNode)
    (parentPath : GeneralBorrowExposedNonleafPrimaryPath.Path entry.allocation.extra selected parent)
    (parentTagEq : parentNode.tag = parentTag)
    (nodeRoom : entry.allocation.extra.nodes.size+1 ≤ 4294967295)
    (short : entry.allocation.extra.nodes.size < 65536)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (S05CompletedAncestryReadMutable.Authority entry.allocation.extra completion tracker.global.protectedTags parent)
      offset (offset+len) entry.allocation.extra.locations)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination true) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[RootReferenceFacts.destination true].value = .live (.immediate .uninit))
    (destUncached : frame.locals[RootReferenceFacts.destination true].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (CopyHelperSteps.advance
        (ActualLocalCopy.written frame (RootReferenceFacts.destination true) (layout true) validDest value.imm)
        (RootReferenceFacts.location true)) resultMachine,.ok true) := by
  obtain ⟨ctx⟩ := ActualReferenceContext.exists_context options remaining span preciseOff implicitOff
  have query := RootReferenceFacts.compute_destination frames frame machine sourceBody identity callee true
  have different : RootReferenceFacts.destination true ≠ 1 := by decide
  have evaluated := rvalue options limits remaining span ctx debugOff cmp .Erased dynamicFuel validityFuel fuelEq validationFuel
    base offset len id entry positive nonzero signedFits frames frame machine tracker enabled
    defaultMode fresh parentTag bounds completion runtime complete order position selected parent selectedNode parentNode slot selectedPresent parentPresent parentPath parentTagEq nodeRoom short owned capacity (RootReferenceFacts.destination true) different validSource validDest sourceLive sourceCached
    destLive destUncached query noClocks ghost shallow cachedAddress present race metadata notConstructed
  let inner := config options remaining span
  let value := RetagReferencePlace.sliceValue inner.access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
  let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
    memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
  let resultFrame := ActualLocalCopy.written frame (RootReferenceFacts.destination true) (layout true) validDest value.imm
  apply CopyHelperSteps.assign_of_actual_rvalue (PreparedContracts.actualConfig options () (remaining+1) span) limits
    frames frame resultFrame machine resultMachine (RootReferenceFacts.location true)
    ⟨RootReferenceFacts.destination true,#[]⟩ (.Ref .Erased (RootReferenceRvalue.borrowKind true) ⟨1,#[.Deref]⟩) located
  · simpa [resultFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout] using located
  · rw [sourceBody]
    exact RootReferenceFacts.statement true
  · exact evaluated

/-- The next actual root shared-Ref statement consumes the original proposal
and installed entry certificates. Graph, authority and node budgets are derived
from those outputs; the physical/frame equalities bind this step to its state. -/
theorem statement_from_entry
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (RootReferenceFacts.location true))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parentTag : BorTag)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat)
    (original : CandidateCurrentJointCall.Before) (originalTracker : MachineHooks.BorrowState)
    (argument : DuplicatePrefixSliceArgument.Argument) (place : MPlaceTy Provenance)
    (call : CandidateStableCallOwnership.CallLoans) (data : CandidateCurrentJointCall.Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span original originalTracker argument len place call data)
    (rawFrame : FrameState)
    (raw : CandidateCurrentFnEntryRaw.Result original originalTracker rawFrame argument len place call data)
    (borrowed : CurrentCallBoolProtection.Borrowed raw) (written : CurrentCallBoolProtection.Written borrowed)
    (entryTree : entry.allocation.extra = sourceTree borrowed)
    (currentGlobal : tracker.global = borrowed.output.global)
    (currentTag : parentTag = raw.output.tag)
    (currentOffset : offset = UInt64.ofNat call.sourceOffset)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination true) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[RootReferenceFacts.destination true].value = .live (.immediate .uninit))
    (destUncached : frame.locals[RootReferenceFacts.destination true].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (CopyHelperSteps.advance
        (ActualLocalCopy.written frame (RootReferenceFacts.destination true) (layout true) validDest value.imm)
        (RootReferenceFacts.location true)) resultMachine,.ok true) := by
  obtain ⟨runtime,complete,order,owned⟩ := source_ready input rawFrame raw borrowed written
  obtain ⟨node,nodeAt,nodeTag⟩ := source_node raw borrowed written
  rw [←entryTree,←currentGlobal] at runtime
  rw [←entryTree] at complete order nodeAt
  rw [←entryTree,←currentGlobal,←currentOffset] at owned
  obtain ⟨position,selected,selectedNode,slot,selectedAt,path⟩ := CandidateCurrentWindowAuthority.root_path
    entry.allocation.extra runtime.formed.toGraphState raw.child node nodeAt
  obtain ⟨_,nodeRoom,short⟩ := source_budget input rawFrame raw borrowed written
  rw [←entryTree] at nodeRoom short
  have tagEq : node.tag = parentTag := nodeTag.trans currentTag.symm
  exact statement options limits remaining span preciseOff implicitOff debugOff cmp dynamicFuel validityFuel fuelEq validationFuel
    base offset len id entry positive nonzero signedFits frames frame machine sourceBody identity callee located tracker enabled defaultMode fresh
    parentTag bounds (sourceCompletion borrowed) runtime complete order position selected raw.child selectedNode node slot selectedAt nodeAt path
    tagEq nodeRoom short owned capacity validSource validDest sourceLive sourceCached destLive destUncached noClocks ghost shallow cachedAddress
    present race metadata notConstructed

/-- Full actual entry and pure prefix followed by the actual shared-Ref MIR
statement. Its physical, graph, metadata and resource inputs are all derived
from the original proposal and the actual entry outputs. -/
theorem invoke {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) (count : UInt64) (nonzero : count ≠ 0) :
    ∃ out : CurrentCallEntry.Output input #[], CurrentCallEntry.Facts out count ∧ ∃ frame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (out.frame count) (out.machine count))
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span (out.machine count))) ∧
      GenericFunctionEntryPrefix.Shape (out.frame count) frame count ∧
      ∃ (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (base : UInt64)
        (fresh : out.borrowed.output.global.nextPointerTag.value < 18446744073709551615)
        (valid : RootReferenceFacts.destination true < frame.locals.size),
      let current := RootZeroCompleteState.tick options remaining span (out.machine count)
      let currentTracker : MachineHooks.BorrowState := ⟨out.borrowed.output.global,.Default⟩
      let offset := UInt64.ofNat call.sourceOffset
      let value := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete call.sourceId currentTracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
      let result := {ReferenceBorrowDriver.allocatedMachine current currentTracker fresh with
        memory := RetagEntry.updatedMemory current.memory call.sourceId entry
          (child entry.allocation.extra currentTracker.global.protectedTags out.source.base.raw.output.tag
            currentTracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
      entry.allocation.extra = sourceTree out.borrowed ∧
      ExecutionMachine.step (config options (remaining+1) span) limits () (Storage.withCurrent #[] frame current) =
        (Storage.withCurrent #[] (CopyHelperSteps.advance
          (ActualLocalCopy.written frame (RootReferenceFacts.destination true) (layout true) valid value.imm)
          (RootReferenceFacts.location true)) result,.ok true) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (out.frame count) (out.machine count))
        (Storage.withCurrent #[] (CopyHelperSteps.advance
          (ActualLocalCopy.written frame (RootReferenceFacts.destination true) (layout true) valid value.imm)
          (RootReferenceFacts.location true)) result) ∧
      (out.machine count).memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,entry) ∧
      (out.machine count).user.addresses.baseAddr.find? (fun row => row.allocId == call.sourceId) = some ⟨call.sourceId,base⟩ := by
  obtain ⟨out,facts,frame,trace,shape⟩ := CurrentCallEntry.invoke_until_shared_reference input stackReady memoryReady positive count nonzero
  let original := CurrentCallPush.preparedMachine before #[]
  let transported := CurrentCallPush.prepared_input input #[]
  let raw := out.source.base.raw
  let current := RootZeroCompleteState.tick options remaining span (out.machine count)
  let currentTracker : MachineHooks.BorrowState := ⟨out.borrowed.output.global,.Default⟩
  let offset := UInt64.ofNat call.sourceOffset
  obtain ⟨entry,sourceLive,tree,bytes,length,_,_,_,_,_⟩ := facts.source_allocation positive
  change entry.allocation.extra = sourceTree out.borrowed at tree
  obtain ⟨windowEntry,base,windowLive,cached,storage,room,bounds,addressEq,nonnull,_⟩ := facts.sourceWindow
  have sameEntry : windowEntry = entry := (Prod.mk.inj (Option.some.inj (windowLive.symm.trans sourceLive))).2
  subst windowEntry
  have offsetBound : call.sourceOffset < 2^64 := by omega
  have offsetEq : offset.toNat = call.sourceOffset := by simp only [offset,UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetBound]
  have sumEq : (base+offset).toNat = base.toNat+call.sourceOffset := by
    simp only [UInt64.toNat_add,offsetEq,Nat.mod_eq_of_lt (by omega : base.toNat+call.sourceOffset<2^64)]
  have bits : raw.sourcePointer.value.offset.bytes = base+offset :=
    UInt64.toNat_inj.mp (addressEq.trans sumEq.symm)
  have pointerEq : CurrentCallTypedFnEntry.changedPointer raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag =
      Pointer.new (.concrete call.sourceId raw.output.tag) (Size.ofBytes (base+offset)) := by
    rw [raw.tag]
    cases ptr : raw.sourcePointer.value with | mk pointerOffset provenance =>
      cases pointerOffset
      simp_all only [CurrentCallTypedFnEntry.changedPointer,Pointer.new,Size.ofBytes]
  have nonnullBits : base+offset ≠ 0 := by
    rw [←bits]
    exact nonnull
  have addresses : current.user.addresses = (out.machine count).user.addresses := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have types : current.user.payload.payload.user.types = (out.machine count).user.payload.payload.user.types := by
    unfold current RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have cachedCurrent : current.user.addresses.baseAddr.find? (fun row => row.allocId == call.sourceId) = some ⟨call.sourceId,base⟩ := by
    rw [addresses];exact cached
  have liveCurrent : current.memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,entry) := sourceLive
  have model := out.settings count
  have originalMode : tracker.retagMode = .Default := by
    obtain ⟨other,enabled,mode⟩ := input.machine.settings.defaultTracker
    have same : other = tracker := Option.some.inj (enabled.symm.trans input.machine.state.enabled)
    simpa only [same] using mode
  obtain ⟨boolRoom,globalEq⟩ := borrowed_global transported {} raw out.borrowed
  have enabled : current.borrowTracker = some currentTracker := by
    change some (⟨(GeneralBorrowFnEntryRegistration.registered raw.output.global raw.output.frame call.returnId out.room).1,tracker.retagMode⟩ : MachineHooks.BorrowState) = some currentTracker
    dsimp only [currentTracker]
    rw [originalMode,globalEq]
  have budget := source_budget transported {} raw out.borrowed facts.written
  have fresh : currentTracker.global.nextPointerTag.value < 18446744073709551615 := budget.1
  obtain ⟨_,_,_,_,_,rawSize⟩ := CandidateCurrentLiveRuntime.live options limits remaining original tracker len
    transported.machine.state transported.machine.resources call.sourceId raw.sourceAllocation raw.sourcePresent
  have capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize := by
    have sizeNat : entry.allocation.extra.locations.size.bytes.toNat = entry.allocation.byteSize.bytes.toNat := by
      rw [tree,source_capacity raw out.borrowed facts.written,rawSize,←length,storage]
    exact congrArg Size.ofBytes (UInt64.toNat_inj.mp sizeNat)
  have treeBounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat := by
    rw [capacity,←storage,offsetEq]
    exact bounds
  have signed : len.toNat < 9223372036854775808 := by
    rcases input.actual.sourceValue with ⟨zero,_⟩ | ⟨_,allocation,_,physical⟩
    · simp [zero] at positive
    · exact physical.signedSize
  have positiveUInt : (0 : UInt64) < len := by simpa only [UInt64.lt_iff_toNat_lt,UInt64.toNat_zero] using positive
  let initial := CurrentCallEntry.root before #[] place input.machine.settings.noDataRace
  let sourceValue := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (CurrentCallTypedFnEntry.changedPointer raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag)
    len ActualReferenceMetadata.reference).imm
  have rawLocals : initial.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := RootEntryFrame.raw_locals _ _ _
  have frameEq := facts.frame_installed
  change out.frame count = PositiveRootInstalledFrame.installed initial sourceValue count {} call.sourceId
    tracker.global.nextPointerTag out.physical.id raw.output.global.nextPointerTag at frameEq
  have oldSource := PositiveRootInstalledFrame.slot_option initial rawLocals sourceValue count {} call.sourceId
    tracker.global.nextPointerTag out.physical.id raw.output.global.nextPointerTag ⟨1,by decide⟩
  rw [←frameEq] at oldSource
  have sourceCell := shape.slot1.trans oldSource
  have v1 : (1 : MIR.LocalId) < frame.locals.size := by rw [shape.size];decide
  have v12 : RootReferenceFacts.destination true < frame.locals.size := by rw [shape.size];decide
  have sourceStored := Option.some.inj ((Array.getElem?_eq_getElem v1).symm.trans sourceCell)
  have sourceValueEq : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete call.sourceId raw.output.tag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm) := by
    have baseEq : (config options remaining span).access.runtime.base = (config options (remaining+1) span).access.runtime.base := by
      rw [CanonicalConfigFacts.actual_access_runtime,CanonicalConfigFacts.actual_access_runtime]
    simpa [sourceValue,pointerEq,baseEq] using congrArg LocalState.value sourceStored
  obtain ⟨body,identity,callee,_,_,_,clocks,_,_⟩ := PositiveRootInstalledFrame.metadata initial sourceValue count {}
    call.sourceId tracker.global.nextPointerTag out.physical.id raw.output.global.nextPointerTag
  rw [←frameEq] at body identity callee clocks
  have destStored := Option.some.inj ((Array.getElem?_eq_getElem v12).symm.trans shape.slot12)
  have metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] frame current)).metadata = PreparedReflection.actual.runtime := by
    change current.user.payload.payload.user.types.metadata = _
    rw [types];exact model.metadata
  have origins : DuplicatePrefixTypeCacheOrigins.Origins current.user.payload.payload.user.types := by
    rw [types];exact out.cacheOrigins count
  have absent := DuplicatePrefixTypeCacheOrigins.slice_not_constructed current.user.payload.payload.user.types metadata origins
  let dynamicFuel := options.place.dynamicFuel-1
  let validityFuel := options.limits.validation-1
  have work : 64 ≤ DuplicatePrefixCallSpecification.work before len := by unfold DuplicatePrefixCallSpecification.work;omega
  have dynamicEq : options.place.dynamicFuel = dynamicFuel+1 := by
    have margin := input.machine.resources.dynamicFuel
    dsimp only [dynamicFuel];omega
  have validityEq : options.limits.validation = validityFuel+1 := by
    have margin := input.machine.resources.configuredFuel.2.2.2
    dsimp only [validityFuel];omega
  have actual := statement_from_entry options limits remaining span model.preciseOff model.implicitOff model.debugOff model.nullComparator
    dynamicFuel validityFuel dynamicEq validityEq base offset len call.sourceId entry positiveUInt nonnullBits signed
    #[] frame current (shape.body.trans (body.trans initial.body)) (shape.identity.trans (identity.trans initial.identity)) (shape.callee.trans (callee.trans initial.callee)) shape.location
    currentTracker enabled rfl fresh raw.output.tag treeBounds original tracker argument place call data transported {} raw out.borrowed facts.written
    tree rfl rfl rfl capacity v1 v12 sourceValueEq
    (by simpa [sourceValue] using congrArg LocalState.layout sourceStored)
    (congrArg LocalState.value destStored) (congrArg LocalState.layout destStored)
    (by rw [shape.extra];exact clocks.trans initial.noClocks)
    ((RootZeroCompleteState.tick_ghost options remaining span (out.machine count)).trans model.ghostOff)
    ((RootZeroCompleteState.tick_shallow options remaining span (out.machine count)).trans model.shallow)
    cachedCurrent liveCurrent model.noDataRace metadata absent
  exact ⟨out,facts,frame,trace,shape,entry,base,fresh,v12,tree,actual,
    SuccessfulTrace.append trace (.next actual (.refl _)),sourceLive,cached⟩

end
end DuplicatePrefix.CurrentCallSharedReference
open Lean Elab Command in
run_cmd do
  for declaration in (← getEnv).constants.toList do
    if ((declaration.1.toString.splitOn "DuplicatePrefix.CurrentCallSharedReference.").length != 1) then
      for dependency in (← collectAxioms declaration.1) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current-call shared reference dependency {dependency}"
