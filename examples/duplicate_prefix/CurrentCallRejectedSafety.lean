import duplicate_prefix.CurrentCallLen
import duplicate_prefix.GeneralBorrowScopedRejectedFrameReady
import duplicate_prefix.RootRejectedPrefix
import duplicate_prefix.CurrentCallLenRootData
import duplicate_prefix.CurrentCallEntryRootRelease
import duplicate_prefix.CurrentCallRootReturn
import duplicate_prefix.SuccessfulTraceTerminal
import duplicate_prefix.S04FinalReturnRuleAccounting
namespace DuplicatePrefix.CurrentCallRejectedSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext CurrentCallLen
open CandidateStableCallOwnership GeneralBorrowProjection S05ConcreteProtectedChildCompletion GeneralRangeMapOrigins
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
private theorem tick_model (options remaining span machine)
    (model : DuplicatePrefixCallModel.Model options remaining span machine) :
    DuplicatePrefixCallModel.Model options remaining span (RootZeroCompleteState.tick options remaining span machine) := by
  have flags := RootZeroCompleteState.tick_flags options remaining span machine
  have unchecked := model.unchecked
  have noGc := model.noGc
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at unchecked noGc
  unfold RootZeroCompleteState.tick SourceControl.accounted at flags ⊢
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] at flags ⊢
  exact {model with unchecked := by rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]; exact flags.1.trans unchecked, noGc := by rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]; exact flags.2.trans noGc}

private theorem post_len_budget {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (held : MachineHooks.BorrowState)
    (tree : BorrowTree)
    (counter : held.global.nextPointerTag.value.toNat = s.held.global.nextPointerTag.value.toNat+1)
    (growth : tree.nodes.size ≤ s.entry.allocation.extra.nodes.size+2) :
    held.global.nextPointerTag.value < 18446744073709551615 ∧
      tree.nodes.size+1 ≤ 4294967295 ∧ tree.nodes.size < 65536 ∧
      held.global.nextPointerTag.value.toNat+8 < 2^64 ∧ tree.nodes.size+8 < 65536 := by
  let prepared := CurrentCallPush.prepared_input input #[]
  let raw := s.out.source.base.raw
  obtain ⟨room,_,_⟩ := CurrentCallBoolProtection.return_budget prepared {} raw
  have outputEq : s.out.borrowed.output = CurrentCallTypedFnEntry.literal (CurrentCallBoolProtection.returnTree raw)
      raw.output.global raw.output.frame call.returnId room raw.returnPointer.value.provenance
      (UInt64.ofNat call.returnOffset) 1 := Except.ok.inj (s.out.borrowed.actual.symm.trans
        (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  have first : raw.output.global.nextPointerTag = TypedRetagEmpty.successorTag tracker.global.nextPointerTag raw.tagRoom := by
    rw [raw.outputGlobal];rfl
  have second : s.out.borrowed.output.global.nextPointerTag = TypedRetagEmpty.successorTag raw.output.global.nextPointerTag room := by
    rw [outputEq];rfl
  have firstStep := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag raw.tagRoom
  have secondStep := GenericFunctionEntryNumerics.successor_value raw.output.global.nextPointerTag room
  have sharedStep := GenericFunctionEntryNumerics.successor_value s.out.borrowed.output.global.nextPointerTag s.room
  have firstNat := congrArg (fun tag : BorTag => tag.value.toNat) first
  have secondNat := congrArg (fun tag : BorTag => tag.value.toNat) second
  have heldNat : s.held.global.nextPointerTag.value.toNat = s.out.borrowed.output.global.nextPointerTag.value.toNat+1 := sharedStep
  have reserve := input.machine.resources.tagRoom
  have fresh : held.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change held.global.nextPointerTag.value.toNat < 18446744073709551615
    omega
  have margin : raw.sourceAllocation.extra.nodes.size+16 < 65536 := by
    have present := raw.sourcePresent
    simp only [CandidateStableCallOwnership.Present,CandidateCurrentJointCall.ActualWorld,Array.toList_map] at present
    obtain ⟨⟨id,entry⟩,member,equal⟩ := List.mem_map.mp present
    have allocEq := (Prod.mk.inj equal).2
    change entry.allocation = raw.sourceAllocation at allocEq
    rw [←allocEq]
    exact prepared.machine.resources.nodeRoom (id,entry) member
  have initialGrowth : s.entry.allocation.extra.nodes.size ≤ raw.sourceAllocation.extra.nodes.size+2 := by
    have sourceGrowth := raw.outputGrowth
    have boolGrowth := s.out.borrowed.metadata.growth
    dsimp only [raw] at sourceGrowth boolGrowth ⊢
    rw [s.extra]
    by_cases same : call.sourceId = call.returnId
    · simp only [CurrentCallBoolProtection.returnTree,same,ite_true] at boolGrowth
      simp only [CurrentCallSharedReference.sourceTree,same,ite_true,s.facts.written.nodes]
      omega
    · simp only [CurrentCallSharedReference.sourceTree,same,ite_false]
      omega
  exact ⟨fresh,by omega,by omega,by omega,by omega⟩

private def originalValue {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) : Immediate Provenance :=
  (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (CurrentCallTypedFnEntry.changedPointer s.out.source.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag)
    len ActualReferenceMetadata.reference).imm

private theorem initial_slot {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (i : Fin 25) :
    (s.out.frame count).locals[i.val]? = some (
      if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
      else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
      else if 1 = i.val then ⟨.live (.immediate (originalValue s)),some ActualReferenceMetadata.reference⟩
      else ⟨.dead,none⟩) := by
  let initial := CurrentCallEntry.root before #[] place input.machine.settings.noDataRace
  have raw : initial.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := RootEntryFrame.raw_locals _ _ _
  have slot := PositiveRootInstalledFrame.slot_option initial raw (originalValue s) count {} call.sourceId tracker.global.nextPointerTag
    s.out.physical.id s.out.source.base.raw.output.global.nextPointerTag i
  rw [s.facts.frame_installed]
  exact slot

private theorem initial_control {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) :
    (s.out.frame count).trackCallerArg = none ∧ (s.out.frame count).extra.userRelevance = 255 := by
  let initial := CurrentCallEntry.root before #[] place input.machine.settings.noDataRace
  rw [s.facts.frame_installed]
  exact ⟨(PositiveRootInstalledFrame.track initial (originalValue s) count {} call.sourceId tracker.global.nextPointerTag
    s.out.physical.id s.out.source.base.raw.output.global.nextPointerTag).trans rfl,
    (PositiveRootInstalledFrame.relevance initial (originalValue s) count {} call.sourceId tracker.global.nextPointerTag
    s.out.physical.id s.out.source.base.raw.output.global.nextPointerTag).trans rfl⟩

private theorem before_len_frame {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) :
    GeneralBorrowForestSharedPreLenFrame.Facts s.parent s.frame count s.value.imm := by
  have shape := CurrentCallLenSharedFrame.shape s.out count s.facts s.parent s.shape s.valid s.value
  change s.frame.body = _ ∧ s.frame.bodyIdentity = _ ∧ s.frame.functionInstance = _ ∧ s.frame.locals.size = _ ∧ _ at shape
  have keep (index : Nat) (different : index ≠ 12) : s.frame.locals[index]? = s.parent.locals[index]? := by
    simp [SharedStage.frame,RootReferenceFacts.destination,CopyHelperSteps.advance,ActualLocalCopy.written,
      LocalPlaces.cachePlaceLayout,Ne.symm different]
  refine ⟨shape.1,shape.2.1,shape.2.2.1,shape.2.2.2.1,shape.2.2.2.2.1,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact CopyHelperCleanup.all_immediate_written s.parent 12 SharedReferenceMetadata.sharedLayout s.value.imm s.valid s.shape.immediate
  · rw [keep 0 (by decide),s.shape.slot0]
    simpa using initial_slot s ⟨0,by decide⟩
  · rw [keep 7 (by decide)];exact s.shape.slot7
  · rw [keep 8 (by decide)];exact s.shape.slot8
  · rw [keep 9 (by decide)];exact s.shape.slot9
  · rw [keep 10 (by decide)];exact s.shape.slot10
  · rw [keep 11 (by decide)];exact s.shape.slot11
  · exact shape.2.2.2.2.2.2.2.1
  · rw [keep 13 (by decide),s.shape.keep 13 (by decide)]
    simpa using initial_slot s ⟨13,by decide⟩

theorem returned_frame {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) :
    GeneralBorrowScopedRejectedFrameReady.Facts s.frame s.lenFrame count len s.value.imm := by
  have facts := before_len_frame s
  have valid : 11 < s.frame.locals.size := by rw [facts.size];decide
  exact GeneralBorrowScopedRejectedFrameReady.build s.parent s.frame count len s.value.imm facts valid


private theorem returned_control {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) :
    s.lenFrame.extra=(s.out.frame count).extra ∧ s.lenFrame.returnPlace=(s.out.frame count).returnPlace ∧
      s.lenFrame.returnContinuation=(s.out.frame count).returnContinuation ∧ s.lenFrame.vaList=(s.out.frame count).vaList := by
  exact ⟨s.shape.extra,s.shape.returnPlace,s.shape.continuation,s.shape.vaList⟩

private theorem rejected_prefix {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (held : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some held)
    (model : DuplicatePrefixCallModel.Model options remaining span machine) (outside : len/2 < count) :
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] s.lenFrame machine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span
          (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span machine)))) ∧
      result.body=RootBody.reflected.body.body ∧ result.locals.size=25 ∧ result.location=.mir ⟨10,0⟩ ∧
      result.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      result.extra=s.lenFrame.extra ∧ result.returnPlace=s.lenFrame.returnPlace ∧
      result.returnContinuation=s.lenFrame.returnContinuation ∧ result.vaList=s.lenFrame.vaList ∧
      CopyHelperCleanup.AllImmediate result := by
  have ready := returned_frame s
  have clocks : s.lenFrame.extra.dataRace = none := by
    have shared := CurrentCallLenSharedFrame.shape s.out count s.facts s.parent s.shape s.valid s.value
    exact shared.2.2.2.2.2.1
  have size := ready.size
  have valid (index : Fin 25) : index.val < s.lenFrame.locals.size := by rw [size];exact index.isLt
  have stored (index : Fin 25) (value : LocalState Provenance LocalLayout)
      (atIndex : s.lenFrame.locals[index.val]? = some value) : s.lenFrame.locals[index.val]'(valid index) = value :=
    Option.some.inj ((Array.getElem?_eq_getElem (valid index)).symm.trans atIndex)
  have default : held.retagMode = .Default := by
    obtain ⟨other,otherTracked,mode⟩ := model.defaultTracker
    have same : other = held := Option.some.inj (otherTracked.symm.trans tracked)
    simpa only [same] using mode
  let fuel := options.limits.validation-1
  have work : 64 ≤ DuplicatePrefixCallSpecification.work before len := by unfold DuplicatePrefixCallSpecification.work;omega
  have fuelEq : options.limits.validation = fuel+1 := by
    have margin := input.machine.resources.configuredFuel.2.2.2
    dsimp only [fuel];omega
  obtain ⟨result,trace,body,identity,callee,extra,returnPlace,continuation,varargs,_,size,located,returned,immediate⟩ := RootRejectedPrefix.executes
    options limits remaining span (DuplicatePrefixCallModel.sourceComparator options remaining span machine model)
    model.debugOff fuel fuelEq s.lenFrame machine len count outside size s.value.imm
    (congrArg LocalState.value (stored ⟨12,by decide⟩ _ ready.slot12))
    (congrArg LocalState.value (stored ⟨13,by decide⟩ _ ready.slot13)) (congrArg LocalState.layout (stored ⟨13,by decide⟩ _ ready.slot13))
    (congrArg LocalState.value (stored ⟨0,by decide⟩ _ ready.slot0)) (congrArg LocalState.layout (stored ⟨0,by decide⟩ _ ready.slot0))
    (congrArg LocalState.value (stored ⟨7,by decide⟩ _ ready.slot7))
    (congrArg LocalState.value (stored ⟨8,by decide⟩ _ ready.slot8)) (congrArg LocalState.layout (stored ⟨8,by decide⟩ _ ready.slot8))
    (congrArg LocalState.value (stored ⟨9,by decide⟩ _ ready.slot9)) (congrArg LocalState.layout (stored ⟨9,by decide⟩ _ ready.slot9))
    (congrArg LocalState.value (stored ⟨10,by decide⟩ _ ready.slot10)) (congrArg LocalState.layout (stored ⟨10,by decide⟩ _ ready.slot10))
    (congrArg LocalState.value (stored ⟨11,by decide⟩ _ ready.slot11)) (congrArg LocalState.layout (stored ⟨11,by decide⟩ _ ready.slot11))
    ready.body ready.identity ready.callee ready.location ready.all clocks held tracked default model.ghostOff model.shallow
    model.unchecked model.noGc model.fixedScheduler
  exact ⟨result,trace,body.trans ready.body,size,located,returned,extra,returnPlace,continuation,varargs,immediate⟩

private theorem after_len_window {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tree : BorrowTree)
    (memory : post.memory = RetagEntry.updatedMemory s.machine.memory call.sourceId
      {s.entry with allocation := s.entry.allocation.setExtra s.tree} tree)
    (addresses : post.user.addresses = s.machine.user.addresses) :
    ∃ window : CurrentCallBoolScalarWrite.Window post place,
      window.id=call.returnId ∧ window.offset=UInt64.ofNat call.returnOffset ∧
      window.pointer=s.out.source.base.raw.returnPointer.value ∧
      CandidateCallBindings.WindowBinding post window.pointer window.id window.offset.toNat 1 := by
  obtain ⟨window,idEq,pointerEq,offsetEq,binding⟩ := CurrentCallRootPhysicalWindow.of_entry s.out count s.facts
  have sharedAddresses : s.machine.user.addresses = (s.out.machine count).user.addresses := by
    unfold SharedStage.machine ReferenceBorrowDriver.allocatedMachine RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  obtain ⟨shared,pointer1,id1,offset1,binding1⟩ := CurrentCallRootPhysicalWindow.tree_update window binding
    call.sourceId s.entry s.tree s.live sharedAddresses rfl
  have live : s.machine.memory.live.find? (fun row => row.1 == call.sourceId) =
      some (call.sourceId,{s.entry with allocation := s.entry.allocation.setExtra s.tree}) :=
    StackPopRelease.lookup_commit_same _ call.sourceId s.entry s.tree
  obtain ⟨next,pointer2,id2,offset2,binding2⟩ := CurrentCallRootPhysicalWindow.tree_update shared binding1
    call.sourceId {s.entry with allocation := s.entry.allocation.setExtra s.tree} tree live addresses
    (congrArg (fun memory => memory.live) memory)
  exact ⟨next,id2.trans (id1.trans idEq),offset2.trans (offset1.trans offsetEq),pointer2.trans (pointer1.trans pointerEq),binding2⟩

private theorem source_node {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (positive : 0 < len.toNat) (tree : BorrowTree)
    (old : ∀ index node, s.entry.allocation.extra.nodes.get index = some node →
      ∃ next, tree.nodes.get index = some next ∧ next.tag=node.tag ∧ next.parent=node.parent ∧ next.isExposed=node.isExposed) :
    ∃ node, tree.nodeAt s.out.source.base.raw.child = some node ∧
      node.tag=s.out.source.base.raw.output.tag ∧ node.isExposed=false := by
  obtain ⟨node,present,tag,_,hidden,_⟩ := CurrentCallEntryProtectionData.Facts.source_data s.facts positive
  have initial : s.entry.allocation.extra.nodes.get s.out.source.base.raw.child = some node := by
    rw [s.extra]
    simpa only [CurrentCallSharedReference.sourceTree,s.facts.extra] using present
  obtain ⟨next,atNext,nextTag,_,nextHidden⟩ := old _ node initial
  exact ⟨next,atNext,nextTag.trans tag,nextHidden.trans hidden⟩

private theorem release_current {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (positive : 0 < len.toNat)
    (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (held : MachineHooks.BorrowState)
    (qEntry bEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (qCompletion bCompletion : Completion)
    (qLive : post.memory.live.find? (fun row => row.1 == call.sourceId)=some (call.sourceId,qEntry))
    (bLive : post.memory.live.find? (fun row => row.1 == call.returnId)=some (call.returnId,bEntry))
    (qRuntime : DuplicatePrefixBorrowContract.RuntimeFacts qEntry.allocation.extra held.global)
    (bRuntime : DuplicatePrefixBorrowContract.RuntimeFacts bEntry.allocation.extra held.global)
    (qComplete : Completes qEntry.allocation.extra qCompletion) (bComplete : Completes bEntry.allocation.extra bCompletion)
    (qOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder qEntry.allocation.extra)
    (bOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder bEntry.allocation.extra)
    (sameCompletion : call.sourceId=call.returnId → bCompletion=qCompletion)
    (qNode bNode oldNode : TreeNode)
    (qAt : qEntry.allocation.extra.nodeAt s.out.source.base.raw.child=some qNode)
    (bAt : bEntry.allocation.extra.nodeAt s.out.borrowed.child=some bNode)
    (oldAt : bEntry.allocation.extra.nodeAt s.out.source.base.raw.returnPointer.grant=some oldNode)
    (original : match s.out.source.base.raw.returnPointer.value.provenance with
      | .concrete _ tag => tag=oldNode.tag | .wildcard => oldNode.isExposed=true)
    (qTag : qNode.tag=s.out.source.base.raw.output.tag) (bTag : bNode.tag=s.out.borrowed.output.tag)
    (qHidden : qNode.isExposed=false) (bHidden : bNode.isExposed=false) (bLeaf : bNode.children=#[])
    (qActive : GeneralBorrowFreshActiveWithin.ActiveWithin qEntry.allocation.extra s.out.source.base.raw.child .Write
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len))
    (bActive : GeneralBorrowFreshActiveWithin.ActiveWithin bEntry.allocation.extra s.out.borrowed.child .Write
      (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1))
    (qOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority qEntry.allocation.extra qCompletion held.global.protectedTags s.out.source.base.raw.child)
      (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) qEntry.allocation.extra.locations)
    (bOwned : OwnedOn (S05CompletedAncestryReadMutable.Authority bEntry.allocation.extra bCompletion held.global.protectedTags s.out.borrowed.child)
      (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) bEntry.allocation.extra.locations)
    (edge : bCompletion.parents[s.out.borrowed.child.toNat]?=some (some s.out.source.base.raw.returnPointer.grant))
    (qShort : qEntry.allocation.extra.nodes.size<65536) (bShort : bEntry.allocation.extra.nodes.size<65536)
    (absent : call.sourceId≠call.returnId → bEntry.allocation.extra.indexOfTag s.out.source.base.raw.output.tag=none)
    (bounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ bEntry.allocation.extra.locations.size.bytes.toNat)
    (initial : CurrentCallBoolScalarWrite.Window post place)
    (initialId : initial.id=call.returnId) (initialPtr : initial.pointer=s.out.source.base.raw.returnPointer.value)
    (initialOffset : initial.offset=UInt64.ofNat call.returnOffset)
    (initialBinding : CandidateCallBindings.WindowBinding post initial.pointer initial.id initial.offset.toNat 1) :
    Nonempty (CurrentCallEntryRootRelease.Released post held (CurrentCallEntryRootRelease.Entry.borrowFrame s.out)
      place s.out.source.base.raw.returnPointer.grant call.returnId (UInt64.ofNat call.returnOffset) s.out.source.base.raw.returnPointer.value) := by
  let raw := s.out.source.base.raw
  let frame := CurrentCallEntryRootRelease.Entry.borrowFrame s.out
  have frameTags : frame.protectedTags=#[(call.sourceId,qNode.tag),(call.returnId,bNode.tag)] := by
    simpa only [qTag,bTag] using CurrentCallEntryRootRelease.Entry.frame_tags s.out
  have endpoints := CurrentCallBoolProtection.endpoints (CurrentCallPush.prepared_input input #[]) {} raw positive
  have qPositive : (UInt64.ofNat call.sourceOffset).toNat < (UInt64.ofNat call.sourceOffset+len).toNat := by
    rw [endpoints.1,endpoints.2.2.1];omega
  have bPositive : (UInt64.ofNat call.returnOffset).toNat < (UInt64.ofNat call.returnOffset+1).toNat := by
    rw [endpoints.2.1,endpoints.2.2.2.1];omega
  have output : ∃ memory finalTree,
      StackPopRelease.Plan held.global.protectedTags frame.protectedTags.toList post.memory memory ∧
      memory.live.find? (fun row => row.1 == call.returnId)=some (call.returnId,{bEntry with allocation:=bEntry.allocation.setExtra finalTree}) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree (held.global.endCall frame) ∧ Completes finalTree bCompletion ∧
      finalTree={bEntry.allocation.extra with locations:=finalTree.locations} ∧
      finalTree.locations.size=bEntry.allocation.extra.locations.size ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority finalTree bCompletion (held.global.endCall frame).protectedTags raw.returnPointer.grant)
        (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) finalTree.locations := by
    by_cases same : call.sourceId=call.returnId
    · have entryEq : qEntry=bEntry := by
        rw [same,bLive] at qLive
        exact (Prod.mk.inj (Option.some.inj qLive)).2.symm
      subst qEntry
      have compEq := sameCompletion same
      rw [←compEq] at qOwned
      have different : s.out.borrowed.child≠raw.child := by
        intro equal
        have atSame : bEntry.allocation.extra.nodes.get raw.child = some bNode := by simpa only [equal,BorrowTree.nodeAt] using bAt
        have nodeEq : bNode=qNode := Option.some.inj (atSame.symm.trans qAt)
        exact CurrentCallEntryProtectionData.source_bool_tags_ne raw s.out.borrowed (qTag.symm.trans (nodeEq ▸ bTag))
      have disjoint : (UInt64.ofNat call.sourceOffset+len).toNat ≤ (UInt64.ofNat call.returnOffset).toNat ∨
          (UInt64.ofNat call.returnOffset+1).toNat ≤ (UInt64.ofNat call.sourceOffset).toNat := by
        by_cases left : (UInt64.ofNat call.sourceOffset+len).toNat ≤ (UInt64.ofNat call.returnOffset).toNat
        · exact .inl left
        by_cases after : (UInt64.ofNat call.sourceOffset).toNat ≤ (UInt64.ofNat call.returnOffset).toNat
        · have impossible := endpoints.2.2.2.2.2 same (UInt64.ofNat call.returnOffset) after (by omega)
          omega
        · have earlier := endpoints.2.2.2.2.2 same (UInt64.ofNat call.sourceOffset) (Nat.le_refl _) qPositive
          exact .inr (by omega)
      let first := bEntry.allocation.extra.releaseProtector qNode.tag held.global.protectedTags
      let second := first.tree.releaseProtector bNode.tag held.global.protectedTags
      let middleEntry := {bEntry with allocation:=bEntry.allocation.setExtra first.tree}
      obtain ⟨plan,runtime,complete,shape,capacity,rights⟩ := CurrentCallRootRelease.same_tree_plan bEntry.allocation.extra held.global bCompletion
        bRuntime bComplete bOrder call.returnId frame raw.child s.out.borrowed.child raw.returnPointer.grant qNode bNode
        qAt bAt qHidden bHidden bLeaf different (by simpa only [same] using frameTags) edge
        (UInt64.ofNat call.sourceOffset) len (UInt64.ofNat call.returnOffset) qPositive bPositive disjoint qActive bActive qOwned bOwned bShort
        post.memory bEntry bLive rfl
      let middle := StackPopRelease.commitTree post.memory call.returnId bEntry first.tree
      let memory := StackPopRelease.commitTree middle call.returnId middleEntry second.tree
      refine ⟨memory,second.tree,plan,?_,runtime,complete,shape,capacity,rights⟩
      simpa only [memory,middleEntry,Allocation.setExtra,Allocation.mapExtra] using StackPopRelease.lookup_commit_same middle call.returnId middleEntry second.tree
    · have hiddenFrame : S04ReturnReleaseParent.HiddenFrame bEntry.allocation.extra frame := by
        intro row member index node present tagged
        rw [frameTags] at member
        change row ∈ [(call.sourceId,qNode.tag),(call.returnId,bNode.tag)] at member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with source | dest
        · subst row
          have mapping := bRuntime.formed.allocator.nodeTags index node present
          rw [tagged,qTag] at mapping
          have impossible := absent same
          change bEntry.allocation.extra.indexOfTag raw.output.tag = some index at mapping
          rw [mapping] at impossible
          cases impossible
        · subst row
          have mapping := bRuntime.formed.allocator.nodeTags index node present
          have actual := bRuntime.formed.allocator.nodeTags s.out.borrowed.child bNode bAt
          rw [tagged,actual] at mapping
          have equal := Option.some.inj mapping
          subst index
          have nodeEq := Option.some.inj (present.symm.trans bAt)
          subst node;exact bHidden
      let first := qEntry.allocation.extra.releaseProtector qNode.tag held.global.protectedTags
      let second := bEntry.allocation.extra.releaseProtector bNode.tag held.global.protectedTags
      let middle := StackPopRelease.commitTree post.memory call.sourceId qEntry first.tree
      let memory := StackPopRelease.commitTree middle call.returnId bEntry second.tree
      obtain ⟨plan,runtime,complete,shape,capacity,rights⟩ := CurrentCallRootRelease.different_trees_plan qEntry.allocation.extra bEntry.allocation.extra held.global
        qCompletion bCompletion qRuntime bRuntime qComplete bComplete qOrder bOrder call.sourceId call.returnId (Ne.symm same) frame
        raw.child s.out.borrowed.child raw.returnPointer.grant qNode bNode qAt bAt qHidden bHidden frameTags hiddenFrame edge
        (UInt64.ofNat call.sourceOffset) len (UInt64.ofNat call.returnOffset) qPositive bPositive qActive bActive qOwned bOwned qShort bShort
        post.memory qEntry bEntry qLive bLive rfl rfl
      exact ⟨memory,second.tree,plan,StackPopRelease.lookup_commit_same middle call.returnId bEntry second.tree,runtime,complete,shape,capacity,rights⟩
  obtain ⟨memory,finalTree,plan,finalLive,runtime,complete,shape,capacity,rights⟩ := output
  let final := ActualPopPlan.released post memory held frame
  obtain ⟨window,ptrSame,idSame,offsetSame,binding⟩ := CurrentCallRootPhysicalWindow.plan held.global.protectedTags frame.protectedTags.toList
    post.memory memory plan post final rfl rfl rfl place initial initialBinding
  have idEq := idSame.trans initialId
  have ptrEq := ptrSame.trans initialPtr
  have offsetEq := offsetSame.trans initialOffset
  have entryEq : window.entry={bEntry with allocation:=bEntry.allocation.setExtra finalTree} := by
    have live := window.live
    rw [idEq] at live
    exact (Prod.mk.inj (Option.some.inj (live.symm.trans finalLive))).2
  have treeEq : window.entry.allocation.extra=finalTree := by rw [entryEq];rfl
  have nodes : finalTree.nodes=bEntry.allocation.extra.nodes := by rw [shape]
  refine ⟨{
    memory := memory
    plan := plan
    window := window
    binding := binding
    roleId := idEq
    roleOffset := offsetEq
    rolePointer := ptrEq
    completion := bCompletion
    runtime := ?_
    completes := ?_
    order := ?_
    short := ?_
    node := oldNode
    present := ?_
    provenance := ?_
    bounds := ?_
    owned := ?_ }⟩
  · rw [treeEq];exact runtime
  · rw [treeEq];exact complete
  · rw [treeEq];exact GeneralBorrowParentTagInvariant.nodes_frame _ _ nodes bOrder
  · rw [treeEq,nodes];exact bShort
  · change window.entry.allocation.extra.nodes.get raw.returnPointer.grant=some oldNode
    rw [treeEq,nodes];exact oldAt
  · rw [ptrEq];exact original
  · rw [treeEq,offsetEq,capacity];exact bounds
  · rw [treeEq,offsetEq];exact rights

private theorem finish {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (positive : 0 < len.toNat)
    (result : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (current : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (released : CurrentCallEntryRootRelease.Released machine current borrowFrame place
      s.out.source.base.raw.returnPointer.grant call.returnId (UInt64.ofNat call.returnOffset) s.out.source.base.raw.returnPointer.value)
    (traceBefore : SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] (s.out.frame count) (s.out.machine count)) (Storage.withCurrent #[] result machine))
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness machine call)
    (thread : Miri.Concurrency.ThreadRecord) (activeThread : machine.threads.activeThread?=some thread)
    (tracked : machine.borrowTracker=some current) (frameTracked : result.extra.borrowTracker=some borrowFrame)
    (body : result.body=RootBody.reflected.body.body) (size : result.locals.size=25)
    (located : result.location=.mir ⟨10,0⟩)
    (slot0 : result.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩)
    (returnPlace : result.returnPlace=(s.out.frame count).returnPlace)
    (noClocks : result.extra.dataRace=none) (returnStop : result.returnContinuation=.stop true)
    (noVarargs : result.vaList=#[]) (immediate : CopyHelperCleanup.AllImmediate result) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  let cfg := config options (remaining+1) span
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span result machine
  have active : accounted.threads.activeThread? = some thread := activeThread
  let post : RootState := ⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] result
    (ActualPopPlan.released accounted released.memory current borrowFrame) (thread.topUserRelevantFrame.getD 0)⟩
  have postUser : post.machine.user = accounted.user := by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have addresses : accounted.user.addresses = machine.user.addresses := by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have extras : accounted.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have ghost : accounted.user.payload.ghost = false := by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact model.ghostOff
  have shallow : accounted.user.payload.validation = .Shallow := by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact model.shallow
  have backend : accounted.user.payload.payload.user.backend = .none := by
    unfold accounted S04FinalReturnRuleAccounting.machine SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact model.noBackend
  have postMemory : post.machine.memory.live = (ActualPopPlan.released machine released.memory current borrowFrame).memory.live := by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> rfl
  obtain ⟨window,pointerEq,idEq,offsetEq,entryEq,binding⟩ := CurrentCallRootPhysicalWindow.view released.window released.binding
    (final := post.machine) (by rw [postUser];exact addresses) postMemory
  have enabled : post.machine.borrowTracker = some {current with global := current.global.endCall borrowFrame} := by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have race : post.machine.dataRace = none := by
    unfold post GenericPopFrame.afterRelevanceAt
    split <;> exact model.noDataRace
  have ready : CurrentCallBoolProtection.WindowReady post.machine window.id window.offset.toNat 1 := by
    have original := memoryReady.bool
    have transported := original.transport (show post.machine.user.payload.payload.user.runtime.extras =
      machine.user.payload.payload.user.runtime.extras from by rw [postUser];exact extras)
    rw [idEq,released.roleId,offsetEq,released.roleOffset]
    have normalized := (CurrentCallBoolProtection.endpoints (CurrentCallPush.prepared_input input #[]) {} s.out.source.base.raw positive).2.1
    rw [normalized]
    exact transported
  have completed : (window.entry.allocation.extra.performBorrowAccessRange
      (S04ReturnBorrowBridge.extra window.pointer.provenance) (Size.ofBytes window.offset) (Size.ofBytes 1)
      .Write (current.global.endCall borrowFrame).protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    rw [entryEq,pointerEq,offsetEq]
    exact CurrentCallRootRelease.write_original released.window.entry.allocation.extra (current.global.endCall borrowFrame)
      released.completion released.runtime released.completes released.order s.out.source.base.raw.returnPointer.grant released.node
      released.present released.window.pointer.provenance released.provenance released.window.offset released.bounds released.owned released.short
  have resolved := CurrentCallRootPhysicalWindow.resolve options remaining span post place window binding
  let fuel := options.limits.validation-1
  have fuelEq : options.limits.validation = fuel+1 := by
    have configured := input.machine.resources.configuredFuel.2.2.2
    have lower : 64 ≤ DuplicatePrefixCallSpecification.work before len := by unfold DuplicatePrefixCallSpecification.work;omega
    dsimp only [fuel];omega
  have enabledBefore : accounted.borrowTracker = some current := tracked
  have valid0 : (0 : Miri.MIR.LocalId) < result.locals.size := by rw [size];decide
  have cell0 : result.locals[0] = ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans slot0)
  have destination : result.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩ := by
    rw [returnPlace,s.facts.destination];rfl
  have unchecked := model.unchecked
  have noGc := model.noGc
  have fixed := model.fixedScheduler
  obtain ⟨updated,returned,_,_,_⟩ := CurrentCallRootReturn.step_of_release_copy options limits remaining span result accounted current borrowFrame
    enabledBefore frameTracked released.memory released.plan thread active post rfl body located valid0 noClocks ghost returnStop
    immediate noVarargs place window binding {current with global := current.global.endCall borrowFrame} enabled race
    (by rw [postUser];exact backend) (by rw [postUser];exact ghost) (by rw [postUser];exact shallow)
    ready completed resolved false fuel model.debugOff fuelEq (by rw [cell0]) (by rw [cell0]) destination
    machine rfl unchecked noGc fixed
  let installed := Storage.withCurrent #[] (s.out.frame count) (s.out.machine count)
  let finalState := CanonicalCopy.replaceAllocation post window.id window.entry.kind updated
  have trace : SuccessfulTrace.Trace cfg limits installed finalState := SuccessfulTrace.append traceBefore (.next returned (.refl _))
  have terminal : ExecutionMachine.step cfg limits () finalState = (finalState,.ok false) := rfl
  have empty : finalState.stack.frames = #[] := rfl
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨cfg,limits,fun _ _ => True⟩
  have entry : CallSafety.IsCallEntry 1 installed := ⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 finalState := by
    change finalState.stack.frames.size < 1
    rw [empty];decide
  exact ⟨installed,finalState,s.facts.actual,trace,terminal,empty,
    SuccessfulTrace.no_errors context 1 installed finalState entry trace past,
    SuccessfulTrace.no_ub context 1 installed finalState entry trace past,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩


private theorem reject_from_released {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (positive : 0 < len.toNat)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (held : MachineHooks.BorrowState)
    (tracked : machine.borrowTracker=some held) (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (ready : CurrentCallBoolProtection.ProfileMemoryReadiness machine call)
    (active : ∃ thread,machine.threads.activeThread?=some thread)
    (trace : SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] (s.out.frame count) (s.out.machine count)) (Storage.withCurrent #[] s.lenFrame machine))
    (outside : len/2<count)
    (released : CurrentCallEntryRootRelease.Released machine held (CurrentCallEntryRootRelease.Entry.borrowFrame s.out)
      place s.out.source.base.raw.returnPointer.grant call.returnId (UInt64.ofNat call.returnOffset) s.out.source.base.raw.returnPointer.value) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  obtain ⟨result,bodyTrace,body,size,located,slot0,extra,returnPlace,continuation,varargs,immediate⟩ :=
    rejected_prefix s machine held tracked model outside
  let frame := CurrentCallEntryRootRelease.Entry.borrowFrame s.out
  let beforeReturn := RootZeroCompleteState.tick options remaining span
    (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span machine))
  have viewAddresses : beforeReturn.user.addresses=machine.user.addresses := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  have viewExtras : beforeReturn.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rfl
  obtain ⟨window,pointerEq,idEq,offsetEq,entryEq,binding⟩ := CurrentCallRootPhysicalWindow.view released.window released.binding
    (final:=ActualPopPlan.released beforeReturn released.memory held frame) viewAddresses rfl
  let current : CurrentCallEntryRootRelease.Released beforeReturn held frame place
      s.out.source.base.raw.returnPointer.grant call.returnId (UInt64.ofNat call.returnOffset) s.out.source.base.raw.returnPointer.value := {
    memory := released.memory
    plan := released.plan
    window := window
    binding := binding
    roleId := idEq.trans released.roleId
    roleOffset := offsetEq.trans released.roleOffset
    rolePointer := pointerEq.trans released.rolePointer
    completion := released.completion
    runtime := by rw [entryEq];exact released.runtime
    completes := by rw [entryEq];exact released.completes
    order := by rw [entryEq];exact released.order
    short := by rw [entryEq];exact released.short
    node := released.node
    present := by rw [entryEq];exact released.present
    provenance := by rw [pointerEq];exact released.provenance
    bounds := by rw [entryEq,offsetEq];exact released.bounds
    owned := by rw [entryEq,offsetEq];exact released.owned }
  obtain ⟨thread,threadActive⟩ := active
  have frameControl := CurrentCallEntryRootRelease.Entry.frame_control s.out count s.facts
  have control := returned_control s
  have frameTracked : result.extra.borrowTracker=some frame := by
    rw [extra,control.1]
    exact CurrentCallEntryRootRelease.Entry.frame_tracked s.out count s.facts
  have noClocks : result.extra.dataRace=none := by rw [extra,control.1];exact frameControl.1
  have returnStop : result.returnContinuation=.stop true := by rw [continuation,control.2.2.1];exact frameControl.2.1
  have noVarargs : result.vaList=#[] := by rw [varargs,control.2.2.2];exact frameControl.2.2
  exact finish s positive result beforeReturn held frame current (SuccessfulTrace.append trace bodyTrace)
    (tick_model _ _ _ _ (tick_model _ _ _ _ (tick_model _ _ _ _ model))) (ready.transport viewExtras)
    thread threadActive tracked frameTracked body size located slot0 (returnPlace.trans control.2.1)
    noClocks returnStop noVarargs immediate


/-- Original positive-source invocation with a rejected nonzero count. The
actual Shared/Len calls, root releases and original Bool store are internal. -/
theorem invoke {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) (count : UInt64) (outsideNat : len.toNat/2 < count.toNat) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  have outside : len/2 < count := UInt64.lt_iff_toNat_lt.mpr (by simpa using outsideNat)
  have nonzero : count ≠ 0 := by intro zero;rw [zero,UInt64.toNat_zero] at outsideNat;omega
  obtain ⟨s,root,machine,entry,held,completion,trace,rootEq,rootLocation,rootValue,destination,live,tracked,runtime,complete,owned,
    allocation,memory,addresses,types,model,origins,ready,active,counter,growth,oldNodes,order,capacity,qActive,flags,others,literal⟩ :=
    CurrentCallLen.invoke_after_shared input stackReady memoryReady positive count nonzero
  obtain ⟨qNode,qAt,qTag,qHidden⟩ := source_node s positive entry.allocation.extra oldNodes
  have budgets := post_len_budget s held entry.allocation.extra counter growth
  obtain ⟨boolData⟩ := CurrentCallLenRootData.of_len s positive machine entry held completion
    live runtime complete allocation order capacity budgets.2.2.1 oldNodes others literal
  obtain ⟨initial,idEq,offsetEq,pointerEq,binding⟩ := after_len_window s machine entry.allocation.extra memory addresses
  obtain ⟨released⟩ := release_current s positive machine held entry boolData.entry completion boolData.completion
    live boolData.live runtime boolData.runtime complete boolData.completes order boolData.order boolData.sameCompletion
    qNode boolData.node boolData.originalNode qAt boolData.present boolData.originalPresent boolData.originalProvenance
    qTag boolData.tag qHidden boolData.hidden boolData.leaf qActive boolData.active owned boolData.owned boolData.edge
    budgets.2.2.1 boolData.short boolData.sourceAbsent boolData.bounds initial idEq pointerEq offsetEq binding
  rw [rootEq] at trace
  exact reject_from_released s positive machine held tracked model ready
    (by obtain ⟨thread,active,_⟩ := active;exact ⟨thread,active⟩) trace outside released

end
end DuplicatePrefix.CurrentCallRejectedSafety

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallRejectedSafety." ||
        name.toString.contains "CurrentCallRejectedSafety" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved rejected safety dependency {dependency}"
