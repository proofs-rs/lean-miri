import duplicate_prefix.CurrentCallOrdinaryCurrentSource
import duplicate_prefix.CurrentCallOrdinarySameAllocationBool
import duplicate_prefix.CurrentCallConversionSourceAfterBool
import duplicate_prefix.CurrentCallOrdinaryPositiveFinish
import duplicate_prefix.CurrentCallOrdinaryLiveCurrentSafety
import duplicate_prefix.CurrentCallConversionBoolFacts
import duplicate_prefix.CurrentCallOtherBoolSourceCheckpoint
import duplicate_prefix.CurrentCallSelectedKeyOrigin

/-! The CURRENT-source entry cases retain their actual converter state and
join the original initialization and common all-count continuation. -/
namespace DuplicatePrefix.CurrentCallOrdinaryCurrentSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallOrdinaryInput
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
open Lean Elab Term in
elab "current_entry_rule " suffix:str : term => do
  let found := (← getEnv).constants.toList.filter (fun (name, _) => name.toString.endsWith suffix.getString)
  match found with
  | [(name, _)] => return mkConst name
  | _ => throwError "expected one checked CURRENT entry theorem {suffix.getString}"

private theorem pointer_known (pointer : Pointer Provenance) (id : AllocId) (tag : BorTag) (base offset : UInt64)
    (provenance : pointer.provenance = .concrete id tag) (bits : pointer.offset.bytes = base + offset) :
    pointer = Pointer.new (.concrete id tag) (Size.ofBytes (base + offset)) := by
  cases pointer with
  | mk position provenanceValue =>
    cases position
    simp_all [Pointer.new, Size.ofBytes]

/-- One source ensure also materializes the SAME return allocation. Bool then
uses the LIVE backend, so there is no second conversion or ensure. -/
theorem same {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (family : Family) (offset capacity : UInt64)
    (positive : 0 < len.toNat) (fits : len.toNat < 9223372036854775808)
    (encoding : argument = .pointer family.value) (assigned : input.assignment.Binds input.sourceOccurrence family)
    (charge : CurrentCallPointwiseSpatialCover.ExactCharge input.Fs input.sourceOwner .mut family.allocation offset.toNat len.toNat)
    (selected : SelectedPointer before input.tracker family offset capacity)
    (latentSource : LatentRole before input.tracker family offset len capacity true)
    (latentReturn : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (same : family.allocation = input.returnFamily.allocation) (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  obtain ⟨absent, noFunction, noVaList, registry, ⟨rootTag, provenance, rootCached⟩, source, current, sourceSize, format, physical⟩ := latentSource
  obtain ⟨base, baseCached, baseRoom, address, nonnull, _⟩ := selected
  have extent : source.len = capacity.toNat := by rw [physical.1.1, sourceSize]; rfl
  have bounds : offset.toNat + len.toNat ≤ source.byteSize.bytes.toNat := physical.2.2.1
  have capacityBounds : offset.toNat + len.toNat ≤ capacity.toNat := by simpa only [sourceSize, Size.ofBytes] using bounds
  have sumRoom : base.toNat + offset.toNat < 2^64 := by omega
  have bits : family.value.offset.bytes = base + offset := by
    apply UInt64.toNat_inj.mp
    rw [address, UInt64.toNat_add, Nat.mod_eq_of_lt sumRoom]
  have value := pointer_known family.value family.allocation rootTag base offset provenance bits
  have encoding' : argument = .pointer (Pointer.new (.concrete family.allocation rootTag) (Size.ofBytes (base + offset))) := by rw [encoding, value]
  have nonzero : base + offset ≠ 0 := by rw [← bits]; exact nonnull
  obtain ⟨rest, externStatic, finalAddresses, finalTape, result, doneFrame, wiring, head, rawCopy, scopedCopy, frameBorrow, _, doneEq,
    stage, S, copyReady, sourceId, sourcePointer, sourceAllocation, sourceGrant, sourceTag, sourceLeaf, sourceNodes,
    sourceModel, sourceOrigins, sourceThreads, sourceHeap, sourceTracked, sourceShallow⟩ :=
    CurrentCallOrdinaryCurrentSource.copy family.allocation rootTag base offset input encoding' source current absent noFunction noVaList registry
      rootCached baseCached nonzero positive fits bounds physical (by simpa only [sourceSize, Size.ofBytes] using baseRoom)
  let prepared := CurrentCallPush.preparedMachine before #[]
  let root := CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let fresh := (current_entry_rule ".CurrentCallOrdinaryCurrentSource.fresh") input
  let sourceFnMachine := CurrentCallOrdinaryCurrentSource.rawPost options result.machine family.allocation rootTag
    input.tracker.global.nextPointerTag result.converted result.global.protectedTags offset len
  let sourceMachine : Before := {sourceFnMachine with borrowTracker := some ⟨result.global, input.tracker.retagMode⟩}
  let sourceTracker : MachineHooks.BorrowState := ⟨result.global, input.tracker.retagMode⟩
  let sourceFnTracker : MachineHooks.BorrowState := ⟨result.global, .FnEntry⟩
  let args := RootArgumentsTwo.result (CurrentCallSourceArguments.doneRoot options remaining span root {} family.value len
    family.allocation input.tracker.global.nextPointerTag) count
  let boolFrame := (atSpan args ⟨601⟩).frame
  let BF : FrameState := ({} : FrameState).addProtector family.allocation input.tracker.global.nextPointerTag
  have facts := CurrentCallOrdinarySameAllocationBool.physical_data input latentReturn source
    (by simpa only [same] using current) rootTag (by simpa only [same] using rootCached) base (by simpa only [same] using baseCached)
    result.converted result.attributes result.wellFormed
  have flags : sourceTracker.global.protectedTags = (GeneralBorrowFnEntryRegistration.registered input.tracker.global {} input.returnFamily.allocation fresh).1.protectedTags := by
    exact result.flags
  have tree : stage.output.child.tree = PositiveGlobalTypedReborrow.finalTree rootTag input.tracker.global.nextPointerTag result.converted.byteSize
      (GeneralBorrowFnEntryRegistration.registered input.tracker.global {} input.returnFamily.allocation fresh).1.protectedTags offset len := by
    rw [stage.treeEq, stage.globalEq, result.attributes.size]
    rfl
  have sourceLive : sourceMachine.memory.live.find? (fun row => row.1 == family.allocation) =
      some (family.allocation, ⟨.machine .global, result.converted.mapExtra (fun _ => stage.output.child.tree)⟩) := by
    rw [sourceHeap]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have sourceBase : sourceMachine.user.addresses.baseAddr.find? (fun row => row.allocId == family.allocation) = some ⟨family.allocation, base⟩ := by
    change result.machine.user.addresses.baseAddr.find? _ = _
    rw [result.frame, CurrentCallConversionFiniteFold.state_eq]
    exact result.bases _ _ baseCached
  have sourceExtra : sourceMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == family.allocation) = some (family.allocation, ⟨none, #[]⟩) := by
    change (((result.machine.user.payload.payload.user.runtime.extras.allocations.filter (fun row => row.1 != family.allocation)).push
      (family.allocation, ⟨none, #[]⟩)).find? (fun row => row.1 == family.allocation)) = _
    have noMatch : (fun row : AllocId × MemoryExtras.AllocationExtra Unit =>
        decide ((row.1 != family.allocation) = true ∧ (row.1 == family.allocation) = true)) = (fun _ => false) := by
      funext row
      by_cases equal : row.1 = family.allocation <;> simp [equal]
    have emptyFind : result.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun _ => false) = none := by
      simp [Array.find?_eq_none]
    simp [Array.find?_push, Array.find?_filter, noMatch, emptyFind]
  have rootHere : sourceTracker.global.rootTag? input.returnFamily.allocation = some rootTag := by
    rw [← same]
    exact result.roots _ _ rootCached
  have physicalApart := CurrentCallOrdinarySameAllocationBool.apart input family offset same charge
  obtain ⟨B⟩ := CurrentCallMaterializedRootBoolFrame.positive sourceMachine sourceTracker input.returnFamily rootTag result.converted base input.returnOffset place facts
    input.tracker.global {} offset len fresh positive (by rw [result.attributes.size]; exact bounds)
    ((current_entry_rule ".CurrentCallOrdinaryCurrentSource.cached_below") input family.allocation rootTag rootCached) input.protectorsBelow
    physicalApart flags (.machine .global) (by simpa only [same] using sourceBase) (by simpa only [same] using sourceExtra) rootHere
    (by simpa only [same, tree] using sourceLive)
    (by
      rw [← tree]
      have runtime := S.runtime
      rw [sourceAllocation] at runtime
      exact runtime)
    (by rw [← tree, stage.roots]; simp)
    (by rw [← tree]; exact stage.growth)
    (by rw [← tree, stage.size, result.attributes.size]; rfl)
    (by rw [← tree, stage.roots]; rfl)
    (by rw [← tree]; exact ⟨stage.rootNode, stage.rootAt, stage.rootTag, stage.rootParent, stage.rootDisabled⟩)
  let W : UniformWindow sourceMachine sourceTracker (CurrentCallMaterializedRootBoolFrame.identities input.returnFamily B.completion) 0
      B.physical.id B.physical.offset.toNat 1 .ret := by
    exact {
      loan := B.window.loan, pointer := B.window.pointer, allocation := B.window.allocation, precise := B.window.precise,
      loanAt := B.window.loanAt, pointerAt := B.window.pointerAt, pointerId := by rw [B.physicalId]; exact B.window.pointerId,
      present := by rw [B.physicalId]; exact B.window.present, preciseAt := by rw [B.physicalId]; exact B.window.preciseAt,
      binding := B.window.binding, issued := by rw [B.physicalId]; exact B.window.issued, parents := B.window.parents,
      window := by intro byte hit; apply B.window.window; simpa only [B.physicalId, B.physicalOffset] using hit }
  have boolPointer : B.physical.pointer = W.pointer.value := by rw [B.physicalPointer, B.pointer]; rfl
  have boolAllocation : B.physical.entry.allocation = W.allocation := B.physicalAllocation.trans B.allocation.symm
  have boolRuntime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra sourceTracker.global := by rw [B.allocation]; exact B.runtime
  have boolShort : W.allocation.extra.nodes.size + 1 < 65536 := by
    rw [B.allocation, ← tree]
    have growth := stage.growth
    change stage.output.child.tree.nodes.size + 1 < 65536
    omega
  have freshB : sourceTracker.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have budget := result.rootBudget
    change result.global.nextPointerTag.value.toNat < 18446744073709551615
    omega
  have sourceEntryAllocation : (⟨.machine .global, result.converted.mapExtra (fun _ => stage.output.child.tree)⟩ : LocalAllocation Provenance BorrowTree MiriMemoryKind).allocation = S.role.backing.allocation := sourceAllocation.symm
  have grantDifferent : S.role.backing.id = B.physical.id → S.grant ≠ W.pointer.grant := by
    intro _ equal
    rw [sourceGrant, B.pointer] at equal
    have left := stage.nodeAt
    rw [equal] at left
    have nodeEq := Option.some.inj (left.symm.trans stage.rootAt)
    have edge := stage.physical
    rw [nodeEq, stage.rootParent] at edge
    cases edge
  have separate : ∀byte, Window S.role.backing.id offset.toNat len.toNat byte → Window B.physical.id B.physical.offset.toNat 1 byte → False := by
    rw [sourceId, B.physicalId, B.physicalOffset]
    exact CurrentCallPointwiseSpatialCover.exclusive_separate input.composable charge input.returnCharge
  obtain ⟨retagCtx⟩ := ActualRetagContext.exists_context options (remaining + 1) span input.model.preciseOff input.model.implicitOff
  obtain ⟨output, post, R, currentS, actual, currentReady, currentFamily, currentId, currentTag, currentGrant, retId, retOffset, original,
    tracked, globalEq, stackEq, retTag, growth, rawOperation, finalTags, extra, mutation, postEq⟩ :=
    CurrentCallConversionSourceAfterBool.after_protect_live options (remaining + 1) span retagCtx sourceMachine sourceTracker offset.toNat len S copyReady
      _ (by rw [sourceId]; exact sourceLive) sourceEntryAllocation sourceLeaf sourceNodes _ 0 #[] boolFrame BF rfl (by rfl)
      place B.physical W boolPointer boolAllocation boolRuntime (by simpa only [B.physicalOffset] using B.binding) (by rw [B.allocation]; exact B.distinct) freshB boolShort grantDifferent separate
      sourceModel.ghostOff sourceModel.noDataRace sourceModel.noBackend (by simpa only [B.physicalOffset] using B.ready)
  have postUser : post.machine.user = sourceMachine.user := by rw [postEq]; rfl
  have postThreads : post.machine.threads = sourceMachine.threads := by rw [postEq]; rfl
  have postRace : post.machine.dataRace = sourceMachine.dataRace := by rw [postEq]; rfl
  have postModel := (current_entry_rule ".CurrentCallOrdinaryLiveCurrentSafety.model_move") sourceModel postUser postThreads postRace tracked input.defaultMode
  have postOrigins : DuplicatePrefixTypeCacheOrigins.Origins post.machine.user.payload.payload.user.types := by rw [postUser]; exact sourceOrigins
  have currentIdOld : currentS.role.backing.id = family.allocation := currentId.trans sourceId
  have currentTagOld : currentS.tag = input.tracker.global.nextPointerTag := currentTag.trans sourceTag
  have currentPointer : currentS.role.family.value = CurrentCallTypedFnEntry.changedPointer family.value currentS.role.backing.id currentS.tag := by
    rw [currentFamily, sourcePointer, currentIdOld, currentTagOld, value]
    rfl
  have tagsDifferent : currentS.tag ≠ R.node.tag := by
    rw [currentTagOld, retTag]
    intro equal
    have older := GeneralBorrowParentTagInvariant.parent_below_fresh S.role.backing.allocation.extra sourceTracker.global S.runtime S.grant S.node S.nodeAt
    rw [S.nodeTag, sourceTag, equal] at older
    exact UInt64.lt_irrefl _ older
  have sourceIds : (sourceMachine.memory.live.toList.map Prod.fst).Nodup := by
    rw [sourceHeap]
    exact (current_entry_rule ".CurrentCallOrdinaryLiveCurrentSafety.replace_ids") before.memory.live family.allocation _ input.runtime.allocationIds
  have ids : (post.machine.memory.live.toList.map Prod.fst).Nodup := by
    rw [postEq]
    apply (current_entry_rule ".CurrentCallOrdinaryLiveCurrentSafety.replace_ids")
    exact (current_entry_rule ".CurrentCallOrdinaryLiveCurrentSafety.replace_ids") _ _ _ sourceIds
  have tags : output.global.nextPointerTag.value.toNat + 6 < 18446744073709551615 := by
    have budget := result.rootBudget
    have successor := GenericFunctionEntryNumerics.successor_value sourceTracker.global.nextPointerTag freshB
    rw [globalEq]
    change (TypedRetagEmpty.successorTag sourceTracker.global.nextPointerTag freshB).value.toNat + 6 < _
    rw [successor]
    change result.global.nextPointerTag.value.toNat + 1 + 6 < _
    omega
  have protectionBudget : (ExecutionMachine.callHooks (config options (remaining + 1) span) limits).protectArgument () place
      (Storage.withCurrent #[] boolFrame sourceMachine) = .ok () post := by
    change TypedRetag.protectInPlaceFunctionArgument (config options (remaining + 1) span).retag limits.retag place _ = _
    exact (congrFun (CurrentCallBoolRetagBudget.protect options (remaining + 1) span retagCtx place input.returnLayout
      options.limits.retag limits.retag) _).symm.trans actual
  have repack := (current_entry_rule ".CurrentCallOrdinaryLiveCurrentSafety.repack") stackEq
  rw [repack] at protectionBudget
  have frameEq : doneFrame = (CurrentCallSourceArguments.doneRoot options remaining span root {} family.value len family.allocation input.tracker.global.nextPointerTag).frame := by
    rw [doneEq, value]
    rfl
  rw [frameEq] at rawCopy
  apply CurrentCallOrdinaryPositiveFinish.invoke input family.value encoding count sourceMachine sourceFnMachine post.machine sourceFnTracker
    ⟨output.global, input.tracker.retagMode⟩ offset.toNat currentS currentReady R currentPointer sourceTracked rfl sourceShallow rfl
  · simpa only [currentIdOld, currentTagOld, value] using rawCopy
  · simpa only [currentIdOld, currentTagOld, retId, B.physicalId, retTag, boolFrame, args, BF] using protectionBudget
  · exact tracked
  · exact input.defaultMode
  · exact postModel
  · exact postOrigins
  · exact tagsDifferent
  · intro different
    exact False.elim (different (retId.trans B.physicalId |>.trans same.symm |>.trans currentIdOld.symm))
  · intro _ byte sourceHit returnHit
    rw [currentIdOld] at sourceHit
    rw [retId, B.physicalId, retOffset, B.physicalOffset] at returnHit
    exact CurrentCallPointwiseSpatialCover.exclusive_separate input.composable charge input.returnCharge byte sourceHit returnHit
  · exact ids
  · exact tags
  · exact postThreads.trans sourceThreads

theorem different {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (family : Family) (offset capacity : UInt64)
    (positive : 0 < len.toNat) (fits : len.toNat < 9223372036854775808)
    (encoding : argument = .pointer family.value) (assigned : input.assignment.Binds input.sourceOccurrence family)
    (charge : CurrentCallPointwiseSpatialCover.ExactCharge input.Fs input.sourceOwner .mut family.allocation offset.toNat len.toNat)
    (selected : SelectedPointer before input.tracker family offset capacity)
    (latentSource : LatentRole before input.tracker family offset len capacity true)
    (latentReturn : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (different : family.allocation ≠ input.returnFamily.allocation) (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  obtain ⟨absent, noFunction, noVaList, registry, ⟨rootTag, provenance, rootCached⟩, source, current, sourceSize, format, physical⟩ := latentSource
  obtain ⟨base, baseCached, baseRoom, address, nonnull, _⟩ := selected
  have extent : source.len = capacity.toNat := by rw [physical.1.1, sourceSize]; rfl
  have bounds : offset.toNat + len.toNat ≤ source.byteSize.bytes.toNat := physical.2.2.1
  have capacityBounds : offset.toNat + len.toNat ≤ capacity.toNat := by simpa only [sourceSize, Size.ofBytes] using bounds
  have sumRoom : base.toNat + offset.toNat < 2^64 := by omega
  have bits : family.value.offset.bytes = base + offset := by
    apply UInt64.toNat_inj.mp
    rw [address, UInt64.toNat_add, Nat.mod_eq_of_lt sumRoom]
  have value := pointer_known family.value family.allocation rootTag base offset provenance bits
  have encoding' : argument = .pointer (Pointer.new (.concrete family.allocation rootTag) (Size.ofBytes (base + offset))) := by rw [encoding, value]
  have nonzero : base + offset ≠ 0 := by rw [← bits]; exact nonnull
  obtain ⟨rest, externStatic, finalAddresses, finalTape, result, doneFrame, wiring, head, rawCopy, scopedCopy, frameBorrow, _, doneEq,
    stage, S, copyReady, sourceId, sourcePointer, sourceAllocation, sourceGrant, sourceTag, sourceLeaf, sourceNodes,
    sourceModel, sourceOrigins, sourceThreads, sourceHeap, sourceTracked, sourceShallow⟩ :=
    CurrentCallOrdinaryCurrentSource.copy family.allocation rootTag base offset input encoding' source current absent noFunction noVaList registry
      rootCached baseCached nonzero positive fits bounds physical (by simpa only [sourceSize, Size.ofBytes] using baseRoom)
  let prepared := CurrentCallPush.preparedMachine before #[]
  let root := CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let fresh := (current_entry_rule ".CurrentCallOrdinaryCurrentSource.fresh") input
  let sourceFnMachine := CurrentCallOrdinaryCurrentSource.rawPost options result.machine family.allocation rootTag
    input.tracker.global.nextPointerTag result.converted result.global.protectedTags offset len
  let sourceMachine : Before := {sourceFnMachine with borrowTracker := some ⟨result.global, input.tracker.retagMode⟩}
  let sourceTracker : MachineHooks.BorrowState := ⟨result.global, input.tracker.retagMode⟩
  let sourceFnTracker : MachineHooks.BorrowState := ⟨result.global, .FnEntry⟩
  let args := RootArgumentsTwo.result (CurrentCallSourceArguments.doneRoot options remaining span root {} family.value len
    family.allocation input.tracker.global.nextPointerTag) count
  let boolFrame := (atSpan args ⟨601⟩).frame
  let BF : FrameState := ({} : FrameState).addProtector family.allocation input.tracker.global.nextPointerTag
  have freshB : sourceTracker.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have budget := result.rootBudget
    change result.global.nextPointerTag.value.toNat < 18446744073709551615
    omega
  have initialRootBelow (tag : BorTag) (cached : input.tracker.global.rootTag? input.returnFamily.allocation = some tag) :
      tag.value.toNat < input.tracker.global.nextPointerTag.value.toNat :=
    (current_entry_rule ".CurrentCallOrdinaryCurrentSource.cached_below") input input.returnFamily.allocation tag cached
  have boolAbsent : sourceMachine.memory.live.find? (fun row => row.1 == input.returnFamily.allocation) = none := by
    rw [sourceHeap, CurrentCallOtherAllocationWindow.lookup _ _ _ _ different]
    exact latentReturn.1
  have boolBases : sourceMachine.user.addresses.baseAddr.find? (fun row => row.allocId == input.returnFamily.allocation) =
      before.user.addresses.baseAddr.find? (fun row => row.allocId == input.returnFamily.allocation) := by
    obtain ⟨oldBase, oldCached, _⟩ := input.returnRepresentation
    rw [oldCached]
    change result.machine.user.addresses.baseAddr.find? _ = _
    rw [result.frame, CurrentCallConversionFiniteFold.state_eq]
    exact result.bases _ _ oldCached
  have boolRoots : sourceTracker.global.rootTag? input.returnFamily.allocation = input.tracker.global.rootTag? input.returnFamily.allocation := by
    obtain ⟨oldRoot, _, oldCached⟩ := latentReturn.2.2.2.2.1
    exact (result.roots _ _ oldCached).trans oldCached.symm
  have extraRows : sourceMachine.user.payload.payload.user.runtime.extras.allocations =
      (before.user.payload.payload.user.runtime.extras.allocations.filter (fun row => row.1 != family.allocation)).push
        (family.allocation, ⟨none, #[]⟩) := by
    change ((result.machine.user.payload.payload.user.runtime.extras.allocations.filter _).push _) = _
    rw [result.frame, CurrentCallConversionFiniteFold.state_eq]
    rfl
  have registryB : InitialRegistryVacant sourceMachine input.returnFamily.allocation := by
    unfold InitialRegistryVacant
    rw [extraRows]
    apply Array.any_eq_false.mpr
    intro index valid
    have member := Array.getElem_mem valid
    rcases Array.mem_push.mp member with member | equal
    · obtain ⟨oldIndex, oldValid, oldEq⟩ := Array.mem_iff_getElem.mp (Array.mem_filter.mp member).1
      simpa only [oldEq] using Array.any_eq_false.mp latentReturn.2.2.2.1 oldIndex oldValid
    · rw [equal]
      simp [different]
  have sourceOlder : input.tracker.global.nextPointerTag.value.toNat < sourceTracker.global.nextPointerTag.value.toNat := by
    have older := GeneralBorrowParentTagInvariant.parent_below_fresh S.role.backing.allocation.extra sourceTracker.global S.runtime S.grant S.node S.nodeAt
    rw [S.nodeTag, sourceTag] at older
    exact UInt64.lt_iff_toNat_lt.mp older
  obtain ⟨sourceB, currentB, sizeB, formatB, physicalB⟩ := latentReturn.2.2.2.2.2
  obtain ⟨D0, dFamily, dOffset, dCurrent0⟩ := CurrentCallConversionBoolPhase.from_initial input latentReturn
    (machine := sourceMachine) (tracker := sourceTracker) (frames := #[]) (frame := boolFrame) (borrowFrame := BF)
    rfl (by rfl) freshB boolAbsent (by rw [sourceHeap]; rfl) (by rw [sourceHeap]; rfl) (by rw [sourceHeap]; rfl)
    boolBases boolRoots (by intro tag cached; have older := initialRootBelow tag cached; omega)
    S.runtime.below.protectors registryB sourceModel.noDataRace sourceModel.ghostOff sourceModel.noBackend
  have samePayload : D0.source = sourceB := CurrentCallOrdinarySameAllocationBool.current_unique dCurrent0 currentB
  let D : CurrentCallConversionBoolPhase.CurrentData sourceMachine sourceTracker #[] boolFrame BF place :=
    {enabled := D0.enabled, frameBorrow := D0.frameBorrow, fresh := D0.fresh,
      family := D0.family, root := D0.root, source := sourceB, base := D0.base, offset := D0.offset,
      value := D0.value, physicalPointer := D0.physicalPointer, layout := D0.layout, aligned := D0.aligned,
      physical := by simpa only [samePayload] using D0.physical,
      current := by simpa only [samePayload] using D0.current,
      absent := D0.absent, noFunction := D0.noFunction, noVaList := D0.noVaList, cached := D0.cached,
      rootCached := D0.rootCached, addressRoom := by simpa only [samePayload] using D0.addressRoom,
      nonnull := D0.nonnull, rootBelow := D0.rootBelow, protectors := D0.protectors, registry := D0.registry,
      race := D0.race, ghost := D0.ghost, backend := D0.backend}
  have dCurrent : CurrentPayload before input.returnFamily.allocation D.source := currentB
  have sourceQuery : CurrentCallConversionPlan.sourceQuery before argument len = .ok (some family.allocation) := by
    rw [encoding']
    exact CurrentCallConversionPlanAdequacy.query_concrete before _ len family.allocation rootTag base rfl baseCached
  have returnQuery := CurrentCallConversionPlanAdequacy.return_query options limits remaining span before argument len place input
  have sourcePayload := CurrentCallConversionPlanAdequacy.payload_of_current before family.allocation source absent noFunction noVaList current
  have returnPayload := CurrentCallConversionPlanAdequacy.payload_of_current before input.returnFamily.allocation D.source
    latentReturn.1 latentReturn.2.1 latentReturn.2.2.1 dCurrent
  have headBoth : CurrentCallConversionPlan.selectedPayloads before argument len place = source :: D.source :: [] := by
    unfold CurrentCallConversionPlan.selectedPayloads
    rw [CurrentCallConversionPlan.selected_of_queries before argument len place _ _ sourceQuery returnQuery,
      CurrentCallConversionPlan.distinct_ids before family.allocation input.returnFamily.allocation source D.source different sourcePayload returnPayload]
    rfl
  have restEq : rest = [D.source] := (List.cons.inj (head.symm.trans headBoth)).2
  change rest = [sourceB] at restEq
  subst rest
  have infoKnown : before.memory.getAllocInfo family.allocation =
      .ok ⟨(result.converted.mapExtra (fun _ => stage.output.child.tree)).byteSize,
        (result.converted.mapExtra (fun _ => stage.output.child.tree)).align, .liveData,
        (result.converted.mapExtra (fun _ => stage.output.child.tree)).mutability⟩ := by
    change before.memory.getAllocInfo family.allocation = .ok ⟨result.converted.byteSize, result.converted.align, .liveData, result.converted.mutability⟩
    rw [result.attributes.size, result.attributes.align, result.attributes.mutability]
    cases current with
    | memory descriptor => exact GlobalDataOnlyMaterialize.alloc_info before _ source absent noFunction noVaList descriptor
    | internalStatic definition descriptor initializer => exact StaticGlobalAllocInfo.alloc_info before _ source definition absent noFunction noVaList descriptor
  have phaseInfo (id : AllocId) : D.registered.machine.memory.getAllocInfo id = before.memory.getAllocInfo id := by
    change sourceMachine.memory.getAllocInfo id = _
    rw [sourceHeap]
    exact CurrentCallConversionMaterialize.metadata_frame before family.allocation .global
      (result.converted.mapExtra (fun _ => stage.output.child.tree)) infoKnown id
  let firstPhase := (registeredState #[]
    (CurrentCallTypedSourceCopy.copiedFrame options remaining span (firstLive root).frame 1
      (by simpa only [i1] using (firstLive root).valid i1)
      (Pointer.new (.concrete family.allocation rootTag) (Size.ofBytes (base + offset))) len) {}
    (allocatedMachine (CurrentCallReferenceEntry.view prepared input.tracker .FnEntry true)
      ⟨input.tracker.global, .FnEntry⟩ fresh)
    (allocatedTracker ⟨input.tracker.global, .FnEntry⟩ fresh) family.allocation input.tracker.global.nextPointerTag)
  let firstTracker := registeredTracker (allocatedTracker ⟨input.tracker.global, .FnEntry⟩ fresh) input.tracker.global.nextPointerTag
  have phaseCounter : D.next.global.nextPointerTag.value.toNat ≤ result.global.nextPointerTag.value.toNat + 1 := by
    have successor := GenericFunctionEntryNumerics.successor_value sourceTracker.global.nextPointerTag freshB
    change (TypedRetagEmpty.successorTag sourceTracker.global.nextPointerTag freshB).value.toNat ≤ _
    rw [successor]
    exact Nat.le_refl _
  have beforeCached : ∃oldBase, before.user.addresses.baseAddr.find? (fun row => row.allocId == family.allocation) = some oldBase :=
    ⟨⟨family.allocation, base⟩, baseCached⟩
  have allBases (id : AllocId) (oldBase : Miri.Memory.AllocAddresses.BaseAddressEntry)
      (hit : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some oldBase) :
      D.registered.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some oldBase := by
    change result.machine.user.addresses.baseAddr.find? _ = _
    rw [result.frame, CurrentCallConversionFiniteFold.state_eq]
    exact result.bases id oldBase hit
  let phase : CurrentCallConversionBoolPhase.NextPhase input D := {
    initial := firstPhase.machine, oldTracker := firstTracker, firstSource := source, rest := [], head := headBoth,
    externStatic := externStatic, wiring := wiring, oldReserve := 15, finalAddresses := finalAddresses, finalTape := finalTape,
    previous := result, initialInfo := by intro id; rfl, infoEq := phaseInfo,
    addresses := by
      change result.machine.user.addresses = result.addresses
      rw [result.frame, CurrentCallConversionFiniteFold.state_eq],
    tape := by
      change EvalPointerSource.tape.get result.machine = result.tape
      rw [result.frame, CurrentCallConversionFiniteFold.state_eq]
      rfl,
    thread := by
      change sourceMachine.threads.activeThread = prepared.threads.activeThread
      exact congrArg (fun threads => threads.activeThread) sourceThreads, roots := by intro id; rfl,
    spent := 1, reserve := 14, room := by decide, positive := by decide, counter := phaseCounter,
    bases := allBases, metadata := by
      intro id member
      exact CurrentCallConversionTargetMetadataFrame.transport before D.registered.machine family.allocation
        ⟨.machine .global, result.converted.mapExtra (fun _ => stage.output.child.tree)⟩ sourceHeap beforeCached allBases
        id (CurrentCallOrdinaryConversionSelected.targets_metadata input id (by
          simp only [CurrentCallConversionPlan.selectedIds, headBoth, List.flatMap_cons, List.flatMap_nil]
          apply List.mem_append_right
          apply List.mem_append_left
          simpa only [CurrentCallConversionFiniteFold.targets_eq] using member)) }
  obtain ⟨retagCtx⟩ := ActualRetagContext.exists_context options (remaining + 1) span input.model.preciseOff input.model.implicitOff
  obtain ⟨boolResult, ⟨protectedOutput⟩⟩ := CurrentCallConversionBoolPhase.next input retagCtx D phase
  let finalMachine := protectedOutput.post.machine
  let next : MachineHooks.BorrowState := {D.next with global := boolResult.global}
  let R := protectedOutput.output
  have postLive := CurrentCallConversionBoolFacts.live D externStatic _ _ _ _ _ boolResult protectedOutput
  have postAddresses := CurrentCallConversionBoolFacts.addresses D externStatic _ _ _ _ _ boolResult protectedOutput
  have postExtras := CurrentCallConversionBoolFacts.extras D externStatic _ _ _ _ _ boolResult protectedOutput
  have postModel := CurrentCallConversionBoolFacts.model D externStatic _ _ _ _ _ boolResult protectedOutput sourceModel input.defaultMode
  have postOrigins := CurrentCallConversionBoolFacts.origins D externStatic _ _ _ _ _ boolResult protectedOutput sourceOrigins
  have postThreads := CurrentCallConversionBoolFacts.threads D externStatic _ _ _ _ _ boolResult protectedOutput
  have boolDifferent : D.family.allocation ≠ S.role.backing.id := by rw [dFamily, sourceId]; exact Ne.symm different
  have postPresent : Present (ActualWorld finalMachine) S.role.backing.id S.role.backing.allocation := by
    have old := S.role.backing.live
    simp only [Present, ActualWorld, Array.toList_map] at old ⊢
    obtain ⟨row, member, equal⟩ := List.mem_map.mp old
    have rowId : row.1 = S.role.backing.id := (Prod.mk.inj equal).1
    apply List.mem_map.mpr
    refine ⟨row, Array.mem_toList_iff.mpr ?_, equal⟩
    change row ∈ finalMachine.memory.live
    rw [postLive]
    apply Array.mem_push.mpr
    apply Or.inl
    apply Array.mem_filter.mpr
    exact ⟨Array.mem_toList_iff.mp member, by simpa only [rowId, bne_iff_ne] using Ne.symm boolDifferent⟩
  have postBinding : CandidateCallBindings.WindowBinding finalMachine S.role.family.value S.role.backing.id offset.toNat len.toNat := by
    obtain ⟨oldEntry, base, oldLookup, oldCache, storage, room, bound, address, nonnull, provenance⟩ := S.binding
    refine ⟨oldEntry, base, ?_, ?_, storage, room, bound, address, nonnull, ?_⟩
    · rw [postLive, CurrentCallOtherAllocationWindow.lookup _ _ _ _ boolDifferent]
      exact oldLookup
    · rw [postAddresses]
      exact boolResult.bases _ _ oldCache
    · rw [S.concrete]
  have selectedRoot : next.global.rootTag? S.role.backing.id = sourceTracker.global.rootTag? S.role.backing.id := by
    let byte : AllocId × Nat := (S.role.backing.id, offset.toNat)
    have inSource : Window S.role.backing.id offset.toNat len.toNat byte := ⟨rfl, Nat.le_refl _, by dsimp [byte]; omega⟩
    obtain ⟨i, inside⟩ := S.role.covered byte inSource
    obtain ⟨rootNode, _, _, _, cachedRoot⟩ := (S.role.roles i ⟨byte, inSource, inside⟩).issued.capability.rootNode
    have newRoot : boolResult.global.rootTag? S.role.backing.id = some rootNode.tag := boolResult.roots _ _ cachedRoot
    exact newRoot.trans cachedRoot.symm
  have selectedExtras : finalMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == S.role.backing.id) =
      sourceMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == S.role.backing.id) := by
    rw [postExtras, CurrentCallOtherAllocationWindow.lookup _ _ _ _ boolDifferent]
  obtain ⟨current, copyReady, currentFamily, currentId, currentAllocation, _, currentTag, currentGrant, currentNode, _⟩ :=
    CurrentCallOtherBoolSourceCheckpoint.at_post S copyReady BF D.family.allocation freshB finalMachine next
      postPresent postBinding selectedRoot boolResult.flags boolResult.counter selectedExtras
  have currentIdOld : current.role.backing.id = family.allocation := currentId.trans sourceId
  have currentTagOld : current.tag = input.tracker.global.nextPointerTag := currentTag.trans sourceTag
  have currentPointer : current.role.family.value = CurrentCallTypedFnEntry.changedPointer family.value current.role.backing.id current.tag := by
    rw [currentFamily, sourcePointer, currentIdOld, currentTagOld, value]
    rfl
  have tagsDifferent : current.tag ≠ R.node.tag := by
    rw [currentTagOld, protectedOutput.tag]
    intro equal
    have numeric := congrArg (fun tag : BorTag => tag.value.toNat) equal
    change input.tracker.global.nextPointerTag.value.toNat = sourceTracker.global.nextPointerTag.value.toNat at numeric
    omega
  have rootOld : input.tracker.global.rootTag? input.returnFamily.allocation = some D.root := by
    have cached := D.rootCached
    change sourceTracker.global.rootTag? D.family.allocation = some D.root at cached
    rw [dFamily, boolRoots] at cached
    exact cached
  have rootDifferent : D.root ≠ current.tag := by
    have older := initialRootBelow D.root rootOld
    rw [currentTagOld]
    intro equal
    rw [equal] at older
    omega
  have rootGrant : R.original.grant = allocationRoot := by rw [protectedOutput.original]; rfl
  have rootValue : R.original.value.provenance = .concrete R.id D.root := by
    rw [protectedOutput.original, protectedOutput.id]
    change D.family.value.provenance = .concrete D.family.allocation D.root
    rw [D.value]
    rfl
  have absent := CurrentCallLazyBoolTagSeparation.absent R D.root current.tag protectedOutput.nodes rootGrant rootValue rootDifferent tagsDifferent
  have sourceIds : (sourceMachine.memory.live.toList.map Prod.fst).Nodup :=
    by
      rw [sourceHeap]
      exact (current_entry_rule ".CurrentCallOrdinaryLiveCurrentSafety.replace_ids") before.memory.live family.allocation _ input.runtime.allocationIds
  have ids : (finalMachine.memory.live.toList.map Prod.fst).Nodup := by
    rw [postLive]
    exact (current_entry_rule ".CurrentCallOrdinaryLiveCurrentSafety.replace_ids") sourceMachine.memory.live D.family.allocation ⟨.machine .global, R.window.allocation⟩ sourceIds
  have tags : next.global.nextPointerTag.value.toNat + 6 < 18446744073709551615 := by
    have budget := boolResult.rootBudget
    change boolResult.global.nextPointerTag.value.toNat + _ + 14 < 2^64 at budget
    change boolResult.global.nextPointerTag.value.toNat + 6 < 18446744073709551615
    omega
  have protectionBudget : (ExecutionMachine.callHooks (config options (remaining + 1) span) limits).protectArgument () place
      (Storage.withCurrent #[] boolFrame sourceMachine) = .ok () protectedOutput.post := by
    change TypedRetag.protectInPlaceFunctionArgument (config options (remaining + 1) span).retag limits.retag place _ = _
    exact (congrFun (CurrentCallBoolRetagBudget.protect options (remaining + 1) span retagCtx place input.returnLayout
      options.limits.retag limits.retag) _).symm.trans protectedOutput.actual
  have repack : protectedOutput.post = Storage.withCurrent #[]
      (registeredFrame boolFrame BF D.family.allocation sourceTracker.global.nextPointerTag) finalMachine := by
    exact (current_entry_rule ".CurrentCallOrdinaryLiveCurrentSafety.repack") protectedOutput.stack
  rw [repack] at protectionBudget
  have copyFinal :
      (ExecutionMachine.callHooks (config options (remaining + 1) span) limits).copyAllowTransmute ()
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span family.value len).imm, ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace 0 (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
        (Storage.withCurrent #[] (firstLive root).frame (ScopedFrame.entered prepared input.tracker .FnEntry)) =
        .ok () (Storage.withCurrent #[] (CurrentCallSourceArguments.doneRoot options remaining span root {} family.value len
          current.role.backing.id current.tag).frame sourceFnMachine) := by
    rw [doneEq] at rawCopy
    simpa only [currentIdOld, currentTagOld, value, CurrentCallSourceArguments.doneRoot] using rawCopy
  have protectionFinal :
      (ExecutionMachine.callHooks (config options (remaining + 1) span) limits).protectArgument () place
        (Storage.withCurrent #[] (atSpan (RootArgumentsTwo.result (CurrentCallSourceArguments.doneRoot options remaining span root {}
          family.value len current.role.backing.id current.tag) count) ⟨601⟩).frame sourceMachine) =
        .ok () (Storage.withCurrent #[] (registeredFrame (atSpan (RootArgumentsTwo.result
          (CurrentCallSourceArguments.doneRoot options remaining span root {} family.value len current.role.backing.id current.tag) count) ⟨601⟩).frame
          (({} : FrameState).addProtector current.role.backing.id current.tag) R.id R.node.tag) finalMachine) := by
    simpa only [currentIdOld, currentTagOld, R, boolFrame, args, BF, protectedOutput.id, protectedOutput.tag] using protectionBudget
  exact CurrentCallOrdinaryPositiveFinish.invoke input family.value encoding count sourceMachine sourceFnMachine finalMachine
    sourceFnTracker next offset.toNat current copyReady R currentPointer sourceTracked rfl sourceShallow rfl copyFinal protectionFinal
    protectedOutput.tracked input.defaultMode postModel postOrigins tagsDifferent (fun _ => absent)
    (by intro same; have idEq := protectedOutput.id; rw [dFamily] at idEq; exact False.elim (different (currentIdOld.symm.trans same.symm |>.trans idEq)))
    ids tags (postThreads.trans sourceThreads)

end
end DuplicatePrefix.CurrentCallOrdinaryCurrentSafety
