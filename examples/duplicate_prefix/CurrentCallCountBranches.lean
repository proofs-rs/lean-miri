import duplicate_prefix.CurrentCallAsMutBoolData
import duplicate_prefix.CurrentCallDefaultMutableBoolData
import duplicate_prefix.CurrentCallLenRootData
import duplicate_prefix.CurrentCallLen
import duplicate_prefix.GeneralBorrowScopedRejectedFrameReady
import duplicate_prefix.RootRejectedPrefix
import duplicate_prefix.GenericLenAcceptedPrelude
import duplicate_prefix.CurrentCallMutableReference
import duplicate_prefix.CurrentCallAsMutArgumentCopy
import duplicate_prefix.S05CurrentMutableProtectorRelease
import duplicate_prefix.S05CompletedChildReanchor
import duplicate_prefix.AsMutReturnFromReleaseRuntime

/-! Literal count guards after the actual current-call Len return. Frame facts
are derived from the installed entry and preceding actual local writes. -/
namespace DuplicatePrefix.CurrentCallCountBranches
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

private theorem shared_addresses {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) :
    s.machine.user.addresses = (s.out.machine count).user.addresses := by
  unfold SharedStage.machine ReferenceBorrowDriver.allocatedMachine RootZeroCompleteState.tick SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  rfl

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

private theorem returned_frame {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) :
    GeneralBorrowScopedRejectedFrameReady.Facts s.frame s.lenFrame count len s.value.imm := by
  have facts := before_len_frame s
  have valid : 11 < s.frame.locals.size := by rw [facts.size];decide
  exact GeneralBorrowScopedRejectedFrameReady.build s.parent s.frame count len s.value.imm facts valid

/-- The actual out-of-bounds count branch reaches immediate false without a
copy. This consumes the original current-call entry and actual Len return. -/
theorem rejected {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) (count : UInt64) (outside : len/2 < count) :
    ∃ (s : SharedStage input count) (result : CompilerFrameContext.ActualFrame)
      (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (s.out.frame count) (s.out.machine count)) (Storage.withCurrent #[] result post) ∧
      result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      result.returnPlace = (s.out.frame count).returnPlace := by
  have nonzero : count ≠ 0 := by
    intro zero
    have bound := UInt64.lt_iff_toNat_lt.mp outside
    rw [zero,UInt64.toNat_zero] at bound
    omega
  obtain ⟨s,root,machine,entry,held,completion,trace,rootEq,_,_,destination,_,tracked,_,_,_,_,_,_,_,model,_,_,_⟩ :=
    CurrentCallLen.invoke_after_shared input stackReady memoryReady positive count nonzero
  have ready := returned_frame s
  have clocks : s.lenFrame.extra.dataRace = none := by
    have shared := CurrentCallLenSharedFrame.shape s.out count s.facts s.parent s.shape s.valid s.value
    exact shared.2.2.2.2.2.1
  rw [rootEq] at trace destination
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
  obtain ⟨result,body,_,_,_,_,returnPlace,_,_,_,_,located,returned,_⟩ := RootRejectedPrefix.executes
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
  exact ⟨s,result,_,SuccessfulTrace.append trace body,located,returned,returnPlace.trans destination⟩

private theorem returned_keep {options limits remaining span before tracker argument len place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data}
    {count : UInt64} (s : SharedStage input count) (index : Nat) (different11 : index ≠ 11) (different12 : index ≠ 12) :
    s.lenFrame.locals[index]? = s.parent.locals[index]? := by
  simp [SharedStage.lenFrame,SharedStage.frame,RootReferenceFacts.destination,LenUncachedFrontend.cachedCaller,
    PtrMetadataExecution.writeFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,
    Ne.symm different11,Ne.symm different12]

/-- The accepted count guard and literal frame preparation reach the actual
mutable-reference statement. This proves no copy or final return yet. -/
theorem accepted {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) (count : UInt64) (nonzero : count ≠ 0) (within : count ≤ len/2) :
    ∃ (s : SharedStage input count) (result : CompilerFrameContext.ActualFrame)
      (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (held : MachineHooks.BorrowState) (completion : Completion),
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (s.out.frame count) (s.out.machine count)) (Storage.withCurrent #[] result post) ∧
      result.location = .mir ⟨6,7⟩ ∧
      result.locals[1]? = (s.out.frame count).locals[1]? ∧
      result.locals[2]? = (s.out.frame count).locals[2]? ∧
      result.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.locals[16]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.returnPlace = (s.out.frame count).returnPlace ∧ CopyHelperCleanup.AllImmediate result ∧
      post.memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,entry) ∧
      post.borrowTracker = some held ∧
      DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra held.global ∧
      Completes entry.allocation.extra completion ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority entry.allocation.extra completion held.global.protectedTags s.out.source.base.raw.child)
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) entry.allocation.extra.locations ∧
      entry.allocation = s.entry.allocation.setExtra entry.allocation.extra ∧
      DuplicatePrefixCallModel.Model options remaining span post ∧
      DuplicatePrefixTypeCacheOrigins.Origins post.user.payload.payload.user.types ∧
      CurrentCallBoolProtection.ProfileMemoryReadiness post call ∧
      (∃ thread, post.threads.activeThread? = some thread ∧ thread.topUserRelevantFrame = some 0) ∧
      held.global.nextPointerTag.value.toNat = s.held.global.nextPointerTag.value.toNat+1 ∧
      entry.allocation.extra.nodes.size ≤ s.entry.allocation.extra.nodes.size+2 ∧
      result.body = RootBody.reflected.body.body ∧
      result.bodyIdentity = RootBody.reflected.body.identity ∧
      result.functionInstance = RootBody.reflected.functionInstance ∧
      result.locals.size = 25 ∧ result.extra = s.lenFrame.extra ∧
      result.extra.dataRace = none ∧ GenericLenAcceptedPrelude.FrameFacts s.lenFrame result ∧
      CandidateCallBindings.WindowBinding post
        (CurrentCallTypedFnEntry.changedPointer s.out.source.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag)
        call.sourceId call.sourceOffset len.toNat ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra ∧
      entry.allocation.extra.locations.size = entry.allocation.byteSize ∧
      (∃ node, entry.allocation.extra.nodes.get s.out.source.base.raw.child = some node ∧
        node.tag = tracker.global.nextPointerTag ∧ node.isExposed = false) ∧
      result.trackCallerArg = none ∧ result.extra.userRelevance = 255 ∧
      (∀ index,17≤index → index<25 → result.locals[index]? = some ⟨.dead,none⟩) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra s.out.source.base.raw.child .Write
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) ∧
      Nonempty (CurrentCallLenRootData.Data s post entry held completion) ∧
      post.memory = RetagEntry.updatedMemory (s.out.machine count).memory call.sourceId s.entry entry.allocation.extra ∧
      post.user.addresses = (s.out.machine count).user.addresses := by
  obtain ⟨s,root,machine,entry,held,completion,trace,rootEq,_,_,destination,live,tracked,runtime,complete,owned,allocation,lenMemory,addresses,_,model,origins,profile,actor,counter,growth,oldNodes,order,capacity,sourceActivity,flags,otherLive,witness⟩ :=
    CurrentCallLen.invoke_after_shared input stackReady memoryReady positive count nonzero
  have bData := CurrentCallLenRootData.of_len s positive machine entry held completion live runtime complete allocation order capacity
    (post_len_budget s held entry.allocation.extra counter growth).2.2.1 oldNodes otherLive witness
  have collapsedMemory : machine.memory = RetagEntry.updatedMemory (s.out.machine count).memory call.sourceId s.entry entry.allocation.extra := by
    rw [lenMemory]
    unfold SharedStage.machine ReferenceBorrowDriver.allocatedMachine RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact RetagEntry.updated_memory_twice _ _ _ _ _
  have ready := returned_frame s
  have clocks : s.lenFrame.extra.dataRace = none := by
    have shared := CurrentCallLenSharedFrame.shape s.out count s.facts s.parent s.shape s.valid s.value
    exact shared.2.2.2.2.2.1
  rw [rootEq] at trace destination
  have size := ready.size
  have valid (index : Fin 25) : index.val < s.lenFrame.locals.size := by rw [size];exact index.isLt
  have stored (index : Fin 25) (value : LocalState Provenance LocalLayout)
      (atIndex : s.lenFrame.locals[index.val]? = some value) : s.lenFrame.locals[index.val]'(valid index) = value :=
    Option.some.inj ((Array.getElem?_eq_getElem (valid index)).symm.trans atIndex)
  have high (index : Fin 25) (lower : 13 ≤ index.val) : s.lenFrame.locals[index.val]? = (s.out.frame count).locals[index.val]? :=
    (returned_keep s index.val (by omega) (by omega)).trans (s.shape.keep index.val lower)
  have fifteen : s.lenFrame.locals[15]? = some ⟨.dead,none⟩ := by
    rw [high ⟨15,by decide⟩ (by decide)]
    simpa using initial_slot s ⟨15,by decide⟩
  have sixteen : s.lenFrame.locals[16]? = some ⟨.dead,none⟩ := by
    rw [high ⟨16,by decide⟩ (by decide)]
    simpa using initial_slot s ⟨16,by decide⟩
  have default : held.retagMode = .Default := by
    obtain ⟨other,otherTracked,mode⟩ := model.defaultTracker
    have same : other = held := Option.some.inj (otherTracked.symm.trans tracked)
    simpa only [same] using mode
  let fuel := options.limits.validation-1
  have work : 64 ≤ DuplicatePrefixCallSpecification.work before len := by unfold DuplicatePrefixCallSpecification.work;omega
  have fuelEq : options.limits.validation = fuel+1 := by
    have margin := input.machine.resources.configuredFuel.2.2.2
    dsimp only [fuel];omega
  have countPositive : (0 : UInt64) < count := UInt64.lt_iff_toNat_lt.mpr (by
    have notzero : count.toNat ≠ 0 := by intro zero;exact nonzero (UInt64.toNat_inj.mp zero)
    simp only [UInt64.toNat_zero]
    omega)
  obtain ⟨result,details,frameFacts⟩ := GenericLenAcceptedPrelude.executes_full options limits remaining span
    (DuplicatePrefixCallModel.sourceComparator options remaining span machine model) model.debugOff fuel fuelEq
    s.lenFrame machine len count countPositive within size s.value.imm
    (congrArg LocalState.value (stored ⟨12,by decide⟩ _ ready.slot12))
    (congrArg LocalState.value (stored ⟨13,by decide⟩ _ ready.slot13)) (congrArg LocalState.layout (stored ⟨13,by decide⟩ _ ready.slot13))
    (congrArg LocalState.value (stored ⟨0,by decide⟩ _ ready.slot0)) (congrArg LocalState.layout (stored ⟨0,by decide⟩ _ ready.slot0))
    (congrArg LocalState.value (stored ⟨7,by decide⟩ _ ready.slot7)) (congrArg LocalState.layout (stored ⟨7,by decide⟩ _ ready.slot7))
    (congrArg LocalState.value (stored ⟨15,by decide⟩ _ fifteen)) (congrArg LocalState.layout (stored ⟨15,by decide⟩ _ fifteen))
    (congrArg LocalState.value (stored ⟨16,by decide⟩ _ sixteen)) (congrArg LocalState.layout (stored ⟨16,by decide⟩ _ sixteen))
    (congrArg LocalState.value (stored ⟨8,by decide⟩ _ ready.slot8)) (congrArg LocalState.layout (stored ⟨8,by decide⟩ _ ready.slot8))
    (congrArg LocalState.value (stored ⟨9,by decide⟩ _ ready.slot9)) (congrArg LocalState.layout (stored ⟨9,by decide⟩ _ ready.slot9))
    (congrArg LocalState.value (stored ⟨10,by decide⟩ _ ready.slot10)) (congrArg LocalState.layout (stored ⟨10,by decide⟩ _ ready.slot10))
    (congrArg LocalState.value (stored ⟨11,by decide⟩ _ ready.slot11)) (congrArg LocalState.layout (stored ⟨11,by decide⟩ _ ready.slot11))
    ready.body ready.identity ready.callee ready.location ready.all clocks held tracked default model.ghostOff model.shallow model.unchecked model.noGc model.fixedScheduler
  rcases details with ⟨body,sameBody,sameIdentity,sameCallee,sameExtra,returnPlace,_,_,_,sameTrack,resultSize,located,sourceEq,countEq,live15,live16,all⟩
  have window : CandidateCallBindings.WindowBinding machine
      (CurrentCallTypedFnEntry.changedPointer s.out.source.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag)
      call.sourceId call.sourceOffset len.toNat := by
    obtain ⟨original,base,originalLive,cached,bytes,room,bounds,address,nonnull,provenance⟩ := s.facts.sourceWindow
    have same : original = s.entry := (Prod.mk.inj (Option.some.inj (originalLive.symm.trans s.live))).2
    subst original
    have lenEq : entry.allocation.len = s.entry.allocation.len := by rw [allocation];rfl
    have sizeEq : entry.allocation.byteSize = s.entry.allocation.byteSize := by rw [allocation];rfl
    have unchanged := addresses.trans (shared_addresses s)
    refine ⟨entry,base,live,?_,?_,?_,?_,address,nonnull,?_⟩
    · rw [unchanged];exact cached
    · rw [lenEq,sizeEq];exact bytes
    · rw [lenEq];exact room
    · rw [lenEq];exact bounds
    · rw [unchanged,sizeEq];exact provenance
  obtain ⟨originalNode,initialAt,originalTag,_,originalHidden,_⟩ := CurrentCallEntryProtectionData.Facts.source_data s.facts positive
  have originalAt : s.entry.allocation.extra.nodes.get s.out.source.base.raw.child = some originalNode := by
    rw [s.extra]
    unfold CurrentCallSharedReference.sourceTree
    rw [←s.facts.extra]
    exact initialAt
  obtain ⟨sourceNode,sourceAt,sourceTag,_,sourceHidden⟩ := oldNodes s.out.source.base.raw.child originalNode originalAt
  have sourceTagEq : sourceNode.tag = tracker.global.nextPointerTag := sourceTag.trans (originalTag.trans s.out.source.base.raw.tag)
  refine ⟨s,result,RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span machine),entry,held,completion,SuccessfulTrace.append trace body,located,
    sourceEq.trans ((returned_keep s 1 (by decide) (by decide)).trans s.shape.slot1),
    countEq.trans ((returned_keep s 2 (by decide) (by decide)).trans s.shape.slot2),
    live15,live16,returnPlace.trans destination,all,live,tracked,runtime,complete,owned,allocation,
    tick_model _ _ _ _ (tick_model _ _ _ _ model),?_,?_,actor,counter,growth,
    sameBody.trans ready.body,sameIdentity.trans ready.identity,sameCallee.trans ready.callee,
    resultSize,sameExtra,(congrArg (fun extra => extra.dataRace) sameExtra).trans clocks,frameFacts,?_,order,capacity,⟨sourceNode,sourceAt,sourceTagEq,sourceHidden.trans originalHidden⟩,?_,?_,?_,sourceActivity,?_,?_,?_⟩
  · unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact origins
  · refine ⟨?_,?_⟩
    · intro positiveWindow
      unfold CurrentCallBoolProtection.WindowReady RootZeroCompleteState.tick SourceControl.accounted
      simp only [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      exact profile.source positiveWindow
    · unfold CurrentCallBoolProtection.WindowReady RootZeroCompleteState.tick SourceControl.accounted
      simp only [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      exact profile.bool
  · obtain ⟨current,base,currentLive,cached,bytes,room,bounds,address,nonnull,provenance⟩ := window
    refine ⟨current,base,currentLive,?_,bytes,room,bounds,address,nonnull,?_⟩
    · unfold RootZeroCompleteState.tick SourceControl.accounted
      simp only [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      exact cached
    · unfold RootZeroCompleteState.tick SourceControl.accounted
      simp only [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      exact provenance
  · rw [sameTrack]
    change s.parent.trackCallerArg = none
    rw [s.shape.track]
    exact (initial_control s).1
  · rw [sameExtra]
    change s.parent.extra.userRelevance = 255
    rw [s.shape.extra]
    exact (initial_control s).2
  · intro index lower upper
    rw [frameFacts.high index lower,returned_keep s index (by omega) (by omega),s.shape.keep index (by omega)]
    simpa [show 14≠index by omega,show 13≠index by omega,show 6≠index by omega,show 0≠index by omega,
      show 2≠index by omega,show 1≠index by omega] using initial_slot s ⟨index,upper⟩

  · obtain ⟨data⟩ := bData
    exact ⟨{data with live := data.live}⟩
  · exact collapsedMemory
  · unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact addresses.trans (shared_addresses s)

/-- The accepted original call executes its mutable Ref and the actual AsMutPtr
call/body. Typed successes are derived from the same returned current rights. -/
theorem accepted_as_mut_returned {options limits remaining span before tracker argument len place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (positive : 0 < len.toNat) (count : UInt64) (nonzero : count ≠ 0) (within : count ≤ len/2) :
    ∃ (s : SharedStage input count) (result : CompilerFrameContext.ActualFrame)
      (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (held : MachineHooks.BorrowState)
      (completion : Completion) (returnedChild : UniIndex) (pointer : Pointer Provenance),
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] (s.out.frame count) (s.out.machine count)) (Storage.withCurrent #[] result post) ∧
      result.location = .mir ⟨7,0⟩ ∧ result.returnPlace = (s.out.frame count).returnPlace ∧
      post.memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,entry) ∧
      post.borrowTracker = some held ∧ DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra held.global ∧
      Completes entry.allocation.extra completion ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority entry.allocation.extra completion held.global.protectedTags s.out.source.base.raw.child)
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) entry.allocation.extra.locations ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority entry.allocation.extra completion held.global.protectedTags returnedChild)
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) entry.allocation.extra.locations ∧
      CandidateCallBindings.WindowBinding post pointer call.sourceId call.sourceOffset len.toNat ∧
      result.locals[15]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer (config options (remaining+1) span).access.runtime.base pointer))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      (∃ node, entry.allocation.extra.nodes.get returnedChild = some node ∧ pointer.provenance = .concrete call.sourceId node.tag) ∧
      DuplicatePrefixCallModel.Model options remaining span post ∧
      DuplicatePrefixTypeCacheOrigins.Origins post.user.payload.payload.user.types ∧
      CurrentCallBoolProtection.ProfileMemoryReadiness post call ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder entry.allocation.extra ∧
      entry.allocation.extra.locations.size = entry.allocation.byteSize ∧ entry.allocation.extra.nodes.size < 65536 ∧
      entry.allocation = s.entry.allocation.setExtra entry.allocation.extra ∧
      result.body = RootBody.reflected.body.body ∧ result.bodyIdentity = RootBody.reflected.body.identity ∧
      result.functionInstance = RootBody.reflected.functionInstance ∧ result.locals.size = 25 ∧
      result.extra = (s.out.frame count).extra ∧ result.extra.dataRace = none ∧
      result.trackCallerArg = none ∧ result.extra.userRelevance = 255 ∧ CopyHelperCleanup.AllImmediate result ∧
      (∀ index,17≤index → index<25 → result.locals[index]? = some ⟨.dead,none⟩) ∧
      result.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩ ∧
      (∃ value, result.locals[16]? = some ⟨.live (.immediate value),some ActualReferenceMetadata.reference⟩) ∧
      (∃ thread,post.threads.activeThread? = some thread ∧ thread.topUserRelevantFrame = some 0) ∧
      (∃ node, entry.allocation.extra.nodes.get s.out.source.base.raw.child = some node ∧
        node.tag = tracker.global.nextPointerTag ∧ node.isExposed = false) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra s.out.source.base.raw.child .Write
        (UInt64.ofNat call.sourceOffset) (UInt64.ofNat call.sourceOffset+len) ∧
      (∃ middle middleNode returnedNode,
        completion.parents[returnedChild.toNat]? = some (some middle) ∧
        completion.parents[middle.toNat]? = some (some s.out.source.base.raw.child) ∧
        entry.allocation.extra.nodes.get middle = some middleNode ∧
        entry.allocation.extra.nodes.get returnedChild = some returnedNode ∧
        held.global.protectedTags.contains middleNode.tag = false ∧
        held.global.protectedTags.contains returnedNode.tag = false) ∧
      Nonempty (CurrentCallLenRootData.Data s post entry held completion) ∧
      result.locals[0]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      result.returnContinuation = (s.out.frame count).returnContinuation ∧
      result.vaList = (s.out.frame count).vaList ∧
      post.memory = RetagEntry.updatedMemory (s.out.machine count).memory call.sourceId s.entry entry.allocation.extra ∧
      post.user.addresses = (s.out.machine count).user.addresses ∧
      (∀ node, entry.allocation.extra.nodes.get returnedChild = some node → node.tag ≠ s.out.borrowed.output.tag) := by
  obtain ⟨s,frame,machine,entry,held,completion,trace,located,sourceSlot,countSlot,slot15,destSlot,destination,all,live,tracked,runtime,complete,owned,allocation,
    model,origins,profile,actor,counter,growth,body,identity,callee,size,frameExtra,clocks,acceptedFrame,window,order,capacity,⟨parentNode,parentAt,parentTag,parentHidden⟩,trackNone,relevance,unused,sourceActivity,⟨boolData⟩,machineMemory,machineAddresses⟩ :=
    accepted input stackReady memoryReady positive count nonzero within
  have budgets := post_len_budget s held entry.allocation.extra counter growth
  obtain ⟨windowEntry,base,windowLive,cached,bytes,room,bounds,address,nonnull,_⟩ := window
  have same : windowEntry = entry := (Prod.mk.inj (Option.some.inj (windowLive.symm.trans live))).2
  subst windowEntry
  let offset := UInt64.ofNat call.sourceOffset
  have offsetEq : offset.toNat = call.sourceOffset := by
    dsimp only [offset]
    simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt (by omega : call.sourceOffset<2^64)]
  have sumEq : (base+offset).toNat = base.toNat+call.sourceOffset := by
    simp only [UInt64.toNat_add,offsetEq,Nat.mod_eq_of_lt (by omega : base.toNat+call.sourceOffset<2^64)]
  have bits : s.out.source.base.raw.sourcePointer.value.offset.bytes = base+offset := UInt64.toNat_inj.mp (address.trans sumEq.symm)
  have pointerEq : CurrentCallTypedFnEntry.changedPointer s.out.source.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag =
      Pointer.new (.concrete call.sourceId tracker.global.nextPointerTag) (Size.ofBytes (base+offset)) := by
    unfold CurrentCallTypedFnEntry.changedPointer
    congr 1
    exact congrArg Size.ofBytes bits
  have actualNonzero : base+offset ≠ 0 := by rw [←bits];exact nonnull
  have actualPositive : (0 : UInt64) < len := UInt64.lt_iff_toNat_lt.mpr positive
  have signedFits : len.toNat < 9223372036854775808 := by
    rcases input.actual.sourceValue with ⟨zero,_⟩ | ⟨_,_,_,physical⟩
    · simp [zero] at positive
    · exact physical.signedSize
  have validSource : (1 : MIR.LocalId)<frame.locals.size := by rw [size];decide
  have validDest : RootReferenceFacts.destination false<frame.locals.size := by rw [size];decide
  have sourceAt : frame.locals[1]? = some ⟨.live (.immediate (originalValue s)),some ActualReferenceMetadata.reference⟩ := by
    rw [sourceSlot]
    simpa using initial_slot s ⟨1,by decide⟩
  have sourceStored := Option.some.inj ((Array.getElem?_eq_getElem validSource).symm.trans sourceAt)
  have destStored := Option.some.inj ((Array.getElem?_eq_getElem validDest).symm.trans destSlot)
  have sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete call.sourceId tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm) := by
    have sourceValue := congrArg LocalState.value sourceStored
    simpa only [originalValue,pointerEq,CanonicalConfigFacts.actual_access_runtime] using sourceValue
  have default : held.retagMode = .Default := by
    obtain ⟨other,otherTracked,mode⟩ := model.defaultTracker
    have same : other = held := Option.some.inj (otherTracked.symm.trans tracked)
    simpa only [same] using mode
  let dynamicFuel := options.place.dynamicFuel-1
  let validityFuel := options.limits.validation-1
  have work : 64 ≤ DuplicatePrefixCallSpecification.work before len := by unfold DuplicatePrefixCallSpecification.work;omega
  have dynamicEq : options.place.dynamicFuel = dynamicFuel+1 := by
    have margin := input.machine.resources.dynamicFuel
    dsimp only [dynamicFuel];omega
  have validityEq : options.limits.validation = validityFuel+1 := by
    have margin := input.machine.resources.configuredFuel.2.2.2
    dsimp only [validityFuel];omega
  have actualBounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat := by
    rw [capacity,←bytes,offsetEq];exact bounds
  obtain ⟨step,mutableRuntime,mutableCapacity,mutableGrowth,child,childLookup,mutableComplete,mutableOwned,⟨childNode,childAt,childTag,childHidden⟩,mutableOrder,mutablePreservesActivity,mutableOldCore⟩ := CurrentCallMutableReference.statement options limits remaining span model.preciseOff model.implicitOff model.debugOff model.nullComparator
    dynamicFuel validityFuel dynamicEq validityEq base offset len call.sourceId entry actualPositive actualNonzero signedFits #[] frame machine
    body identity callee located held tracked default budgets.1 tracker.global.nextPointerTag completion runtime complete order
    s.out.source.base.raw.child parentNode parentAt parentTag budgets.2.1 budgets.2.2.1 actualBounds owned capacity validSource validDest sourceLive
    (congrArg LocalState.layout sourceStored) (congrArg LocalState.value destStored) (congrArg LocalState.layout destStored) clocks model.ghostOff model.shallow
    cached live model.noDataRace model.metadata origins
  let mutableTree := (GeneralBorrowRawDefaultExpression.child entry.allocation.extra held.global.protectedTags tracker.global.nextPointerTag held.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
  let mutableTracker := ReferenceBorrowDriver.allocatedTracker held budgets.1
  let mutableEntry := {entry with allocation := entry.allocation.setExtra mutableTree}
  let mutableMachine := {ReferenceBorrowDriver.allocatedMachine machine held budgets.1 with
    memory := RetagEntry.updatedMemory machine.memory call.sourceId entry mutableTree}
  have sourceDisjoint := (CurrentCallBoolProtection.endpoints (CurrentCallPush.prepared_input input #[]) {} s.out.source.base.raw positive).2.2.2.2.2
  have boolDisjoint : call.sourceId = call.returnId → ∀ point : UInt64,
      (UInt64.ofNat call.returnOffset).toNat ≤ point.toNat → point.toNat < (UInt64.ofNat call.returnOffset+1).toNat →
      point.toNat < (UInt64.ofNat call.sourceOffset).toNat ∨ (UInt64.ofNat call.sourceOffset+len).toNat ≤ point.toNat := by
    intro same point lower upper
    by_cases earlier : point.toNat < (UInt64.ofNat call.sourceOffset).toNat
    · exact .inl earlier
    by_cases inside : point.toNat < (UInt64.ofNat call.sourceOffset+len).toNat
    · have impossible := sourceDisjoint same point (by omega) inside
      omega
    · exact .inr (by omega)
  have boolJoined := CurrentCallDefaultMutableBoolData.of_statement s machine entry held completion boolData live runtime complete order
    parentNode parentAt (parentTag.trans s.out.source.base.raw.tag.symm) budgets.1 budgets.2.1
    (by have reserve := budgets.2.2.2.2;omega) (by intro zero;have bad := positive;rw [zero,UInt64.toNat_zero] at bad;omega) actualBounds owned boolDisjoint child
    (by simpa only [CurrentCallDefaultMutableBoolData.borrowedTree,parentTag,offset] using childLookup)
    (by simpa only [CurrentCallDefaultMutableBoolData.borrowedTree,parentTag,offset] using mutableRuntime)
    (by simpa only [CurrentCallDefaultMutableBoolData.borrowedTree,parentTag,offset] using mutableComplete)
    (by simpa only [CurrentCallDefaultMutableBoolData.borrowedTree,parentTag,offset] using mutableOrder)
    (by refine ⟨childNode,?_,childTag⟩;simpa only [CurrentCallDefaultMutableBoolData.borrowedTree,parentTag,offset] using childAt)
    (by simpa only [CurrentCallDefaultMutableBoolData.borrowedTree,parentTag,offset] using mutableOldCore)
  obtain ⟨mutableBoolData⟩ := boolJoined
  let mutableValue := RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete call.sourceId held.global.nextPointerTag) (Size.ofBytes (base+offset))) len (RootReferenceInfo.layout false)
  let mutableFrame := CopyHelperSteps.advance (ActualLocalCopy.written frame (RootReferenceFacts.destination false)
    (RootReferenceInfo.layout false) validDest mutableValue.imm) (RootReferenceFacts.location false)
  have mutableModel : DuplicatePrefixCallModel.Model options remaining span mutableMachine :=
    {model with defaultTracker := ⟨mutableTracker,rfl,default⟩}
  have mutableFresh : mutableTracker.global.nextPointerTag.value < 18446744073709551615 := by
    have increment := GenericFunctionEntryNumerics.successor_value held.global.nextPointerTag budgets.1
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag held.global.nextPointerTag budgets.1).value.toNat < 18446744073709551615
    have reserve := budgets.2.2.2.1
    omega
  have mutableRoom : mutableTree.nodes.size+1 ≤ 4294967295 ∧ mutableTree.nodes.size < 65536 := by
    have reserve := budgets.2.2.2.2
    change mutableTree.nodes.size ≤ entry.allocation.extra.nodes.size+1 at mutableGrowth
    exact ⟨by omega,by omega⟩
  have mutableLive : mutableMachine.memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,mutableEntry) :=
    MemoryCopyBridge.live_lookup_replaced machine.memory call.sourceId mutableEntry
  have mutableSize : mutableFrame.locals.size = 25 := by
    simp only [mutableFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,Array.size_set,size]
  have mutableSlot15 : mutableFrame.locals[15]? = some ⟨.live (.immediate .uninit),none⟩ := by
    simpa [mutableFrame,CopyHelperSteps.advance,ActualLocalCopy.written,RootReferenceFacts.destination,
      LocalPlaces.cachePlaceLayout,Array.getElem?_set] using slot15
  have mutableClocks : mutableFrame.extra.dataRace = none := clocks
  have mutableValid15 : (15 : MIR.LocalId)<mutableFrame.locals.size := by rw [mutableSize];decide
  have mutableValid16 : (16 : MIR.LocalId)<mutableFrame.locals.size := by rw [mutableSize];decide
  have mutableDestStored := Option.some.inj ((Array.getElem?_eq_getElem mutableValid15).symm.trans mutableSlot15)
  have mutableSourceLive : mutableFrame.locals[16].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base
      (Pointer.new (.concrete call.sourceId held.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm) := by
    simp [mutableFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootReferenceFacts.destination,mutableValue]
    rfl
  have mutableSourceCached : mutableFrame.locals[16].layout = some ActualReferenceMetadata.reference := by
    simp [mutableFrame,CopyHelperSteps.advance,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootReferenceFacts.destination]
    rfl
  have mutableBody : mutableFrame.body = RootBody.reflected.body.body := body
  have mutableIdentity : mutableFrame.bodyIdentity = RootBody.reflected.body.identity := identity
  have mutableCallee : mutableFrame.functionInstance = RootBody.reflected.functionInstance := callee
  have mutableDefault : mutableTracker.retagMode = .Default := default
  have mutableCapacityEntry : mutableTree.locations.size = mutableEntry.allocation.byteSize := mutableCapacity.trans capacity
  have mutableBounds : offset.toNat+len.toNat ≤ mutableEntry.allocation.byteSize.bytes.toNat := by
    change offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat
    rw [←bytes,offsetEq];exact bounds
  have mutableOrigins : DuplicatePrefixTypeCacheOrigins.Origins mutableMachine.user.payload.payload.user.types := origins
  obtain ⟨thread,active,top⟩ := actor
  have mutableActive : mutableMachine.threads.activeThread? = some thread := active
  let cachedCaller := AsMutUncachedCall.cachedCaller mutableFrame mutableValid15
  let callState := Storage.withCurrent #[] cachedCaller mutableMachine
  let callDestination := (LocalPlaces.localRuntimePlace 0 cachedCaller 15 CopyCompilerFacts.destPointerLayout).stackView
  have topKnown : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates callState callDestination).stack thread.topUserRelevantFrame = some 0 := by
    simp only [FrameRelevance.top,top,Option.orElse_some]
  have presentKnown : (AsMutPush.pushed options.userRelevantCrates callState callDestination).stack.frames[0]? = some cachedCaller := by
    simp [callState,AsMutPush.pushed,Storage.withCurrent]
  have topAccounted : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates
      (Storage.withCurrent #[] cachedCaller (AsMutPtrReturn.accountedMachine options remaining span mutableMachine))
      callDestination).stack thread.topUserRelevantFrame = some 0 := by
    simp only [FrameRelevance.top,top,Option.orElse_some]
  have presentAccounted : (AsMutPush.pushed options.userRelevantCrates
      (Storage.withCurrent #[] cachedCaller (AsMutPtrReturn.accountedMachine options remaining span mutableMachine))
      callDestination).stack.frames[0]? = some cachedCaller := by
    simp [AsMutPush.pushed,Storage.withCurrent]
  let dispatchFuel := limits.callDispatch-1
  have dispatchEq : limits.callDispatch = dispatchFuel+1 := by
    have margin := input.machine.resources.executionFuel.1
    dsimp only [dispatchFuel];omega
  let ctx := Classical.choice (ActualReferenceContext.exists_context options remaining span model.preciseOff model.implicitOff)
  obtain ⟨raw,rawActual,rawTag,rawGlobal,rawFrame,rawRead,rawChildDone,rawRuntime,rawCapacity,rawGrowth,rawTree,
    rawIndex,rawLookup,rawRoots,rawComplete,rawOwned,rawActivity,rawOrder,rawOld,rawNode,rawPreservesActivity,done,called,helperTrace,helperLocation,helperFacts⟩ :=
    CurrentCallAsMutArgumentCopy.Body.step_from_authority options limits remaining dispatchFuel dispatchEq span ctx
      model.debugOff model.nullComparator dynamicFuel validityFuel dynamicEq validityEq call.sourceId mutableEntry base offset len held.global.nextPointerTag
      actualPositive actualNonzero signedFits mutableBounds mutableFrame mutableMachine mutableTracker rfl mutableDefault mutableFresh
      (extend completion child s.out.source.base.raw.child) mutableRuntime mutableComplete mutableOrder child childNode childAt childTag
      mutableRoom.1 mutableRoom.2 mutableOwned mutableCapacityEntry mutableValid15 .uninit
      (congrArg LocalState.value mutableDestStored) (congrArg LocalState.layout mutableDestStored) mutableClocks mutableModel.ghostOff mutableModel.shallow
      cached mutableLive mutableModel.noDataRace mutableModel.metadata mutableOrigins thread 0 cachedCaller mutableActive topAccounted presentAccounted
      (DuplicatePrefixCallModel.sourceComparator options remaining span mutableMachine mutableModel) mutableBody mutableIdentity mutableCallee rfl
      mutableValid16 mutableSourceLive mutableSourceCached mutableModel.noBackend mutableModel.unchecked mutableModel.noGc mutableModel.fixedScheduler
  obtain ⟨helperNode,helperAt,helperTag,helperHidden⟩ := rawNode
  obtain ⟨helperPosition,helperRoot,helperRootNode,helperSlot,helperRootAt,helperPath⟩ := CandidateCurrentWindowAuthority.root_path
    raw.child.tree rawRuntime.formed.toGraphState rawIndex helperNode helperAt
  have windowPositive : offset.toNat < (offset+len).toNat := by
    have nowrap : offset.toNat+len.toNat < 2^64 := by rw [offsetEq];omega
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt nowrap]
    omega
  have rawShort : raw.child.tree.nodes.size < 65536 := by
    have reserve := budgets.2.2.2.2
    change mutableTree.nodes.size ≤ entry.allocation.extra.nodes.size+1 at mutableGrowth
    change raw.child.tree.nodes.size ≤ mutableTree.nodes.size+1 at rawGrowth
    omega
  obtain ⟨released,releaseFrame,releasedRuntime,releasedComplete,releasedCapacity,releasedOwned⟩ :=
    S05CurrentMutableProtectorRelease.release_owned raw.child.tree raw.global
      (extend (extend completion child s.out.source.base.raw.child) rawIndex child) rawRuntime rawComplete rawOrder
      helperPosition helperRoot rawIndex helperRootNode helperNode helperSlot helperRootAt helperPath helperAt helperHidden
      offset len windowPositive rawActivity rawOwned rawShort
  let releasedTree := (raw.child.tree.releaseProtector helperNode.tag raw.global.protectedTags).tree
  have releaseActual : raw.child.tree.releaseProtector raw.tag raw.global.protectedTags = ⟨releasedTree,.Released⟩ := by
    rw [←helperTag]
    cases equation : raw.child.tree.releaseProtector helperNode.tag raw.global.protectedTags with
    | mk tree status =>
      have same : status = .Released := by simpa only [equation] using released
      simp only [releasedTree,equation,same]
  have releasedNode : releasedTree.nodes.get rawIndex = some helperNode := by
    have nodes := congrArg BorrowTree.nodes releaseFrame
    change releasedTree.nodes = raw.child.tree.nodes at nodes
    rw [nodes];exact helperAt
  have frameEq : raw.frame = ({} : FrameState).addProtector call.sourceId raw.tag := by
    exact congrArg FrameState.mk rawFrame
  have dropped := GeneralBorrowHiddenProtectorDropRuntime.end_call releasedTree raw.global releasedRuntime
    call.sourceId raw.tag rawIndex helperNode releasedNode helperTag helperHidden
  have afterRuntime := dropped.1
  have helperUnheld := dropped.2.1
  rw [←frameEq] at afterRuntime helperUnheld
  have restoredMutable : OwnedOn (S05CompletedAncestryReadMutable.Authority releasedTree
      (extend (extend completion child s.out.source.base.raw.child) rawIndex child)
      (raw.global.endCall raw.frame).protectedTags child) offset (offset+len) releasedTree.locations := by
    apply S05CompletedChildReanchor.owned_end_call releasedTree _ raw.global raw.frame call.sourceId rawIndex child helperNode offset (offset+len)
      (S05ConcreteProtectedChildCompletion.child_edge _ _ _) releasedNode _ releasedOwned
    rw [rawFrame,helperTag]
    simp
  have retainedRawChild : OwnedOn (S05CompletedAncestryReadMutable.Authority releasedTree
      (extend (extend completion child s.out.source.base.raw.child) rawIndex child)
      (raw.global.endCall raw.frame).protectedTags rawIndex) offset (offset+len) releasedTree.locations := by
    intro position valid positive start stop index node present
    have previous := releasedOwned position valid positive start stop index node present
    have weaken := GeneralBorrowRelease.end_call_weakens raw.global raw.frame
    constructor
    · intro below
      have localRights := previous.1 below
      exact ⟨localRights.1,localRights.2.1,localRights.2.2.1,fun held => localRights.2.2.2 (weaken node.tag held)⟩
    · intro outside
      have foreign := previous.2 outside
      exact ⟨foreign.1,fun held => foreign.2 (weaken node.tag held)⟩
  obtain ⟨defaultNode,defaultAt,defaultTag,_,_⟩ := rawOld child childNode childAt
  have older := GeneralBorrowParentTagInvariant.parent_below_fresh mutableTree mutableTracker.global mutableRuntime child childNode childAt
  have differentTag : defaultNode.tag ≠ mutableTracker.global.nextPointerTag := by
    rw [defaultTag]
    intro equal
    rw [equal] at older
    have impossible := UInt64.lt_iff_toNat_lt.mp older
    omega
  have different : child ≠ rawIndex := by
    intro equal
    have equalAt : raw.child.tree.nodes.get rawIndex = some defaultNode := by simpa only [equal] using defaultAt
    have equalNode : defaultNode = helperNode := Option.some.inj (equalAt.symm.trans helperAt)
    exact differentTag ((congrArg (fun node : TreeNode => node.tag) equalNode).trans (helperTag.trans rawTag))
  have firstEdge := S05ConcreteProtectedChildCompletion.child_edge completion child s.out.source.base.raw.child
  have oldEdge : (extend (extend completion child s.out.source.base.raw.child) rawIndex child).parents[child.toNat]? =
      some (some s.out.source.base.raw.child) :=
    (S05ConcreteProtectedChildCompletion.old_parent _ rawIndex child child different (Array.getElem?_eq_some_iff.mp firstEdge).1).trans firstEdge
  have defaultReleasedAt : releasedTree.nodes.get child = some defaultNode := by
    have nodes := congrArg BorrowTree.nodes releaseFrame
    change releasedTree.nodes = raw.child.tree.nodes at nodes
    rw [nodes];exact defaultAt
  have high := GeneralBorrowForestTagHighWater.complete entry.allocation.extra _ _ runtime.below runtime.formed.allocator.nodeTags
  obtain ⟨_,_,originalUnheld⟩ := GenericFunctionTagFormation.fresh_above entry.allocation.extra _ _ held.global.nextPointerTag high (Nat.le_refl _)
  have defaultUnheld : mutableTracker.global.protectedTags.contains defaultNode.tag = false := by
    rw [defaultTag,childTag]
    exact originalUnheld
  have rawDefaultUnheld : raw.global.protectedTags.contains defaultNode.tag = false := by
    rw [rawGlobal]
    have same := ProtectorInsertion.contains_other mutableTracker.global.protectedTags mutableTracker.global.nextPointerTag defaultNode.tag .StrongProtector differentTag
    exact same.trans defaultUnheld
  have finalDefaultUnheld : (raw.global.endCall raw.frame).protectedTags.contains defaultNode.tag = false := by
    cases found : (raw.global.endCall raw.frame).protectedTags.contains defaultNode.tag with
    | false => rfl
    | true =>
      have old := GeneralBorrowRelease.end_call_weakens raw.global raw.frame defaultNode.tag found
      rw [rawDefaultUnheld] at old
      cases old
  have restoredSource : OwnedOn (S05CompletedAncestryReadMutable.Authority releasedTree
      (extend (extend completion child s.out.source.base.raw.child) rawIndex child)
      (raw.global.endCall raw.frame).protectedTags s.out.source.base.raw.child) offset (offset+len) releasedTree.locations := by
    intro position valid positive start stop
    exact S05CompletedChildReanchor.authority releasedTree _ _ _ _ child s.out.source.base.raw.child defaultNode oldEdge defaultReleasedAt
      (fun _ previous => previous) finalDefaultUnheld (restoredMutable position valid positive start stop)
  rcases helperFacts with ⟨retval,_,_,_,_,_,_,_,_,_,helperSize,dead2,dead3,dead4,
    helperRuntime,helperCache,helperFrameTracked,helperRace,helperBody,helperDestination,helperContinuation,helperVarargs,helperArgument⟩
  let helperBefore := Storage.withCurrent #[] cachedCaller (AsMutPtrReturn.accountedMachine options remaining span mutableMachine)
  let helperDest := (LocalPlaces.localRuntimePlace 0 cachedCaller 15 CopyCompilerFacts.destPointerLayout).stackView
  let pushedMachine := (AsMutPush.completed options.userRelevantCrates helperBefore helperDest cachedCaller).machine
  let helperMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine pushedMachine mutableTracker mutableFresh)
      (ReferenceBorrowDriver.allocatedTracker mutableTracker mutableFresh) mutableTracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory pushedMachine.memory call.sourceId mutableEntry
        (CurrentCallAsMutArgumentCopy.Argument.finalTree mutableEntry.allocation.extra mutableTracker held.global.nextPointerTag offset len)}
  let returnedValue : Scalar Provenance := Scalar.fromPointer (config options (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete call.sourceId mutableTracker.global.nextPointerTag) (Size.ofBytes (base+offset)))
  have helperMemory : helperMachine.memory = RetagEntry.updatedMemory pushedMachine.memory call.sourceId mutableEntry raw.child.tree := by
    rw [rawTree]
  have helperTracked : helperMachine.borrowTracker = some (⟨raw.global,.Default⟩ : MachineHooks.BorrowState) := by
    rw [rawGlobal]
    change some (⟨_,mutableTracker.retagMode⟩ : MachineHooks.BorrowState) = some ⟨_,.Default⟩
    rw [mutableDefault]
    rfl
  have cachedValid15 : (15 : MIR.LocalId)<cachedCaller.locals.size := by
    simpa only [cachedCaller,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.size_set] using mutableValid15
  have cachedLive : cachedCaller.locals[15].value = .live (.immediate .uninit) := by
    simpa only [cachedCaller,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self] using congrArg LocalState.value mutableDestStored
  have cachedLayout : cachedCaller.locals[15].layout = some CopyCompilerFacts.destPointerLayout := by
    simp only [cachedCaller,AsMutUncachedCall.cachedCaller,LocalPlaces.cachePlaceLayout,Array.getElem_set_self]
  have cachedClocks : cachedCaller.extra.dataRace = none := mutableClocks
  have argumentAt : done.locals[1]?.map (·.value) = some (.live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete call.sourceId mutableTracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm)) := by
    simp only [helperArgument,Option.map_some]
  obtain ⟨root,post,returned,rootEq,postMemory,postTracked,postRuntime,postCache⟩ :=
    AsMutReturnFromReleaseRuntime.step options limits remaining span model.debugOff validityFuel validityEq #[] cachedCaller done helperMachine returnedValue
      helperBody helperSize _ argumentAt dead2 dead3 dead4 helperRuntime helperLocation retval helperRace helperDestination helperContinuation helperVarargs
      cachedValid15 cachedLive cachedLayout cachedClocks call.sourceId raw.tag mutableEntry raw.child.tree releasedTree pushedMachine.memory helperMemory
      ⟨raw.global,.Default⟩ raw.frame helperTracked helperFrameTracked rawFrame releaseActual helperCache helperRuntime.race helperRuntime.ghost helperRuntime.shallow
  have mutableSourceActivity := mutablePreservesActivity s.out.source.base.raw.child sourceActivity
  have rawSourceActivity := rawPreservesActivity s.out.source.base.raw.child mutableSourceActivity
  have finalSourceActivity := GeneralBorrowActiveWithinRelease.release raw.child.tree raw.global.protectedTags helperNode.tag rawIndex
    s.out.source.base.raw.child helperNode (by rw [helperTag];exact rawLookup) helperAt helperHidden offset (offset+len) rawActivity rawSourceActivity
  obtain ⟨mutableSourceNode,mutableSourceAt,mutableSourceTag,_,mutableSourceHidden⟩ := mutableOldCore s.out.source.base.raw.child parentNode parentAt
  obtain ⟨finalSourceNode,finalSourceAt,finalSourceTag,_,finalSourceHidden⟩ := rawOld s.out.source.base.raw.child mutableSourceNode mutableSourceAt
  have releasedSourceAt : releasedTree.nodes.get s.out.source.base.raw.child = some finalSourceNode := by
    have nodes := congrArg BorrowTree.nodes releaseFrame
    change releasedTree.nodes = raw.child.tree.nodes at nodes
    rw [nodes];exact finalSourceAt
  let finalEntry := {mutableEntry with allocation := mutableEntry.allocation.setExtra releasedTree}
  let finalHeld : MachineHooks.BorrowState := ⟨raw.global.endCall raw.frame,.Default⟩
  let finalCompletion := extend (extend completion child s.out.source.base.raw.child) rawIndex child
  let returnedPointer := Pointer.new (Provenance.concrete call.sourceId raw.tag) (Size.ofBytes (base+offset))
  have finalLive : post.memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,finalEntry) := by
    rw [postMemory]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have helperData : helperMachine.user.addresses = machine.user.addresses ∧
      helperMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      helperMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
    have pushed := AsMutPushPreserves.preserves options.userRelevantCrates helperBefore helperDest cachedCaller
    have userEq := pushed.2.2.2.2.2.2.1
    change pushedMachine.user.payload.payload.user = helperBefore.machine.user.payload.payload.user at userEq
    refine ⟨?_,?_,?_⟩
    · change pushedMachine.user.addresses = machine.user.addresses
      rw [pushed.2.2.2.1]
      unfold helperBefore AsMutPtrReturn.accountedMachine SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl
    · change pushedMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types
      rw [userEq]
      unfold helperBefore AsMutPtrReturn.accountedMachine SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl
    · change pushedMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras
      rw [userEq]
      unfold helperBefore AsMutPtrReturn.accountedMachine SourceControl.accounted
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      rfl
  have postAddresses := postRuntime.addresses.trans helperData.1
  have postTypes := postRuntime.types.trans helperData.2.1
  have postExtras := postRuntime.extras.trans helperData.2.2
  have finalModel : DuplicatePrefixCallModel.Model options remaining span post := {model with
    ghostOff := postRuntime.ghost
    shallow := postRuntime.shallow
    defaultTracker := ⟨finalHeld,postTracked,rfl⟩
    noDataRace := postRuntime.race
    noBackend := postRuntime.backend
    metadata := by rw [postTypes];exact model.metadata
    fixedScheduler := postRuntime.fixed
    unchecked := postRuntime.unchecked
    noGc := postRuntime.noGc}
  have finalOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder releasedTree := by
    have nodes := congrArg BorrowTree.nodes releaseFrame
    change releasedTree.nodes = raw.child.tree.nodes at nodes
    exact GeneralBorrowParentTagInvariant.nodes_frame raw.child.tree _ nodes rawOrder
  have finalShort : releasedTree.nodes.size < 65536 := by
    have nodes := congrArg BorrowTree.nodes releaseFrame
    change releasedTree.nodes = raw.child.tree.nodes at nodes
    rw [nodes];exact rawShort
  have finalCapacity : releasedTree.locations.size = finalEntry.allocation.byteSize :=
    releasedCapacity.trans (rawCapacity.trans mutableCapacityEntry)
  have rootKeep (index : Nat) (not15 : index≠15) (not16 : index≠16) : root.locals[index]? = frame.locals[index]? := by
    rw [rootEq]
    simp [AsMutPtrReturn.writeFrame,cachedCaller,AsMutUncachedCall.cachedCaller,mutableFrame,CopyHelperSteps.advance,
      ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootReferenceFacts.destination,Ne.symm not15,Ne.symm not16]
  have beforeBoolData : CurrentCallLenRootData.Data s mutableMachine mutableEntry mutableTracker
      (extend completion child s.out.source.base.raw.child) := by
    simpa only [CurrentCallDefaultMutableBoolData.borrowedTree,parentTag,offset] using mutableBoolData
  have boolDifferent : call.sourceId = call.returnId → s.out.borrowed.child ≠ child := by
    intro same equal
    have rowEq := beforeBoolData.sameEntry same
    have bAt : mutableTree.nodes.get s.out.borrowed.child = some beforeBoolData.node := by
      have found := beforeBoolData.present
      rw [rowEq] at found
      exact found
    have bAtChild : mutableTree.nodes.get child = some beforeBoolData.node := by simpa only [equal] using bAt
    have nodeEq : beforeBoolData.node = childNode := Option.some.inj (bAtChild.symm.trans childAt)
    have sameTag : boolData.node.tag = held.global.nextPointerTag :=
      boolData.tag.trans (beforeBoolData.tag.symm.trans ((congrArg TreeNode.tag nodeEq).trans childTag))
    have older := GeneralBorrowParentTagInvariant.parent_below_fresh boolData.entry.allocation.extra held.global
      boolData.runtime s.out.borrowed.child boolData.node boolData.present
    have impossible := UInt64.lt_iff_toNat_lt.mp older
    rw [sameTag] at impossible
    omega
  have endpoints := CurrentCallBoolProtection.endpoints (CurrentCallPush.prepared_input input #[]) {} s.out.source.base.raw positive
  have disjointOrder : call.sourceId = call.returnId →
      (UInt64.ofNat call.sourceOffset+len).toNat ≤ (UInt64.ofNat call.returnOffset).toNat ∨
      (UInt64.ofNat call.returnOffset+1).toNat ≤ (UInt64.ofNat call.sourceOffset).toNat := by
    intro same
    by_cases left : (UInt64.ofNat call.sourceOffset+len).toNat ≤ (UInt64.ofNat call.returnOffset).toNat
    · exact .inl left
    by_cases after : (UInt64.ofNat call.sourceOffset).toNat ≤ (UInt64.ofNat call.returnOffset).toNat
    · have impossible := endpoints.2.2.2.2.2 same (UInt64.ofNat call.returnOffset) after (by omega)
      have low := endpoints.2.1
      have high := endpoints.2.2.2.1
      omega
    · have earlier := endpoints.2.2.2.2.2 same (UInt64.ofNat call.sourceOffset) (Nat.le_refl _) windowPositive
      exact .inr (by omega)
  obtain ⟨boolPosition,boolRoot,boolRootNode,boolSlot,boolRootAt,boolPath⟩ := CandidateCurrentWindowAuthority.root_path
    mutableTree mutableRuntime.formed.toGraphState child childNode childAt
  have pushedMemory : pushedMachine.memory = mutableMachine.memory := by
    calc
      pushedMachine.memory = helperBefore.machine.memory :=
        (AsMutPushPreserves.preserves options.userRelevantCrates helperBefore helperDest cachedCaller).1
      _ = mutableMachine.memory := by
        unfold helperBefore AsMutPtrReturn.accountedMachine SourceControl.accounted
        rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
        rfl
  have originalEntry : entry = {s.entry with allocation := s.entry.allocation.setExtra entry.allocation.extra} := by
    have expected : machine.memory.live.find? (fun row => row.1 == call.sourceId) =
        some (call.sourceId,{s.entry with allocation := s.entry.allocation.setExtra entry.allocation.extra}) := by
      rw [machineMemory]
      exact MemoryCopyBridge.live_lookup_replaced _ _ _
    exact (Prod.mk.inj (Option.some.inj (live.symm.trans expected))).2
  have finalMemoryOriginal : post.memory = RetagEntry.updatedMemory (s.out.machine count).memory call.sourceId s.entry releasedTree := by
    calc
      post.memory = RetagEntry.updatedMemory machine.memory call.sourceId entry releasedTree := by
        rw [postMemory,pushedMemory]
        exact RetagEntry.updated_memory_twice _ _ _ _ _
      _ = RetagEntry.updatedMemory (s.out.machine count).memory call.sourceId s.entry releasedTree := by
        rw [machineMemory,originalEntry]
        exact RetagEntry.updated_memory_twice _ _ _ _ _
  have finalBoolJoined := CurrentCallAsMutBoolData.of_return s mutableMachine mutableEntry mutableTracker
    (extend completion child s.out.source.base.raw.child) beforeBoolData mutableRuntime mutableComplete mutableOrder
    boolPosition boolRoot child boolRootNode childNode boolSlot boolRootAt childAt boolPath boolDifferent mutableFresh mutableRoom.1
    (by change mutableTree.nodes.size+1 < 65536
        have reserve := budgets.2.2.2.2
        have growth := mutableGrowth
        change mutableTree.nodes.size ≤ entry.allocation.extra.nodes.size+1 at growth
        omega) (by intro zero;have bad := positive;rw [zero,UInt64.toNat_zero] at bad;omega)
    (by change (UInt64.ofNat call.sourceOffset).toNat+len.toNat ≤ mutableTree.locations.size.bytes.toNat
        rw [mutableCapacity];exact actualBounds) mutableOwned disjointOrder raw rawIndex
    (by simpa only [childTag,offset] using rawActual) rawLookup ⟨helperNode,helperAt,helperTag⟩ post finalEntry finalHeld
    (by rw [←helperTag,←pushedMemory];exact postMemory) finalLive rfl afterRuntime releasedComplete finalOrder
    (by intro index node found
        obtain ⟨next,nextAt,nextTag,nextParent,nextHidden⟩ := rawOld index node found
        refine ⟨next,?_,nextTag,nextParent,nextHidden⟩
        have nodes := congrArg BorrowTree.nodes releaseFrame
        change releasedTree.nodes = raw.child.tree.nodes at nodes
        change releasedTree.nodes.get index = some next
        rw [nodes];exact nextAt)
  obtain ⟨⟨finalBoolData⟩,boolTagFresh⟩ := finalBoolJoined
  have mutableAll : CopyHelperCleanup.AllImmediate mutableFrame :=
    CopyHelperCleanup.all_immediate_written frame _ _ _ validDest all
  have cachedAll : CopyHelperCleanup.AllImmediate cachedCaller :=
    CopyHelperCleanup.all_immediate_cache mutableFrame 15 CopyCompilerFacts.destPointerLayout mutableValid15 mutableAll
  have rootAll : CopyHelperCleanup.AllImmediate root := by
    rw [rootEq]
    exact CopyHelperCleanup.all_immediate_set cachedCaller 15 _ cachedValid15 cachedAll (by intro memory;simp)
  refine ⟨s,root,post,finalEntry,finalHeld,finalCompletion,rawIndex,returnedPointer,
    SuccessfulTrace.append trace (.next step (.next called (SuccessfulTrace.append helperTrace (.next returned (.refl _))))),?_,?_,finalLive,postTracked,
    afterRuntime,releasedComplete,restoredSource,retainedRawChild,?_,?_,⟨helperNode,releasedNode,?_⟩,finalModel,?_,profile.transport postExtras,
    finalOrder,finalCapacity,finalShort,?_,?_,?_,?_,?_,?_,?_,?_,?_,rootAll,?_,?_,?_,postCache rfl,
      ⟨finalSourceNode,releasedSourceAt,finalSourceTag.trans (mutableSourceTag.trans parentTag),
        finalSourceHidden.trans (mutableSourceHidden.trans parentHidden)⟩,finalSourceActivity,
      ⟨child,defaultNode,helperNode,S05ConcreteProtectedChildCompletion.child_edge _ _ _,oldEdge,defaultReleasedAt,releasedNode,
        finalDefaultUnheld,by rw [helperTag];exact helperUnheld⟩,⟨finalBoolData⟩,?_,?_,?_,finalMemoryOriginal,postAddresses.trans machineAddresses,?_⟩
  · rw [rootEq]
  · rw [rootEq]
    exact destination
  · refine ⟨finalEntry,base,finalLive,?_,bytes,room,?_,sumEq,?_,rfl⟩
    · rw [postAddresses];exact cached
    · exact bounds
    · change base+offset ≠ 0
      exact actualNonzero
  · rw [rootEq]
    simp only [AsMutPtrReturn.writeFrame,Array.getElem?_set,Array.getElem?_eq_getElem cachedValid15,ite_true,cachedLayout]
    dsimp only [returnedValue,returnedPointer]
    rw [rawTag]
  · change Provenance.concrete call.sourceId raw.tag = Provenance.concrete call.sourceId helperNode.tag
    rw [helperTag]
  · rw [postTypes];exact origins
  · change (entry.allocation.setExtra mutableTree).setExtra releasedTree = s.entry.allocation.setExtra releasedTree
    rw [allocation]
    rfl
  · rw [rootEq];exact mutableBody
  · rw [rootEq];exact mutableIdentity
  · rw [rootEq];exact mutableCallee
  · rw [rootEq]
    simpa only [AsMutPtrReturn.writeFrame,Array.size_set,cachedCaller,AsMutUncachedCall.cachedCaller,
      LocalPlaces.cachePlaceLayout] using mutableSize
  · rw [rootEq]
    change frame.extra = (s.out.frame count).extra
    exact frameExtra.trans s.shape.extra
  · rw [rootEq];exact clocks
  · rw [rootEq];exact trackNone
  · rw [rootEq];exact relevance
  · intro index lower upper
    rw [rootKeep index (by omega) (by omega)]
    exact unused index lower upper
  · rw [rootKeep 2 (by decide) (by decide),countSlot]
    simpa using initial_slot s ⟨2,by decide⟩
  · refine ⟨mutableValue.imm,?_⟩
    rw [rootEq]
    simp [AsMutPtrReturn.writeFrame,cachedCaller,AsMutUncachedCall.cachedCaller,mutableFrame,CopyHelperSteps.advance,
      ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,RootReferenceFacts.destination]
    rfl

  · rw [rootKeep 0 (by decide) (by decide)]
    exact acceptedFrame.slot0.trans (returned_frame s).slot0
  · rw [rootEq]
    exact acceptedFrame.continuation.trans s.shape.continuation
  · rw [rootEq]
    exact acceptedFrame.varargs.trans s.shape.vaList
  · intro node found equal
    have same : node = helperNode := Option.some.inj (found.symm.trans releasedNode)
    subst node
    apply boolTagFresh
    exact (helperTag.symm.trans equal).symm

end
end DuplicatePrefix.CurrentCallCountBranches
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallCountBranches.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current count branch dependency {dependency}"
