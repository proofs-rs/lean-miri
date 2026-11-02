import duplicate_prefix.CurrentCallOrdinaryLiveSource
import duplicate_prefix.CurrentCallConversionBoolFacts
import duplicate_prefix.CurrentCallOrdinaryPositiveFinish
import duplicate_prefix.CurrentCallOtherBoolSourceCheckpoint
import duplicate_prefix.CurrentCallConversionTargetMetadataFrame
import duplicate_prefix.CurrentCallLazyBoolTagSeparation
import duplicate_prefix.CurrentCallBoolRetagBudget

/-! The SOURCE-LIVE / return-CURRENT entry branch, joined to the common
all-count continuation. The branch data are extracted from OrdinaryInput by
the exhaustive positive dispatcher. -/
namespace DuplicatePrefix.CurrentCallOrdinaryLiveCurrentSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallOrdinaryInput
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

open Lean Elab Term in
elab "live_current_rule " suffix:str : term => do
  let found := (← getEnv).constants.toList.filter (fun (name, _) => name.toString.endsWith suffix.getString)
  match found with
  | [(name, _)] => return mkConst name
  | _ => throwError "expected one checked LIVE/CURRENT theorem {suffix.getString}"

private theorem info_tree (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree)
    (live : memory.live.find? (fun row => row.1 == id) = some (id, entry)) (query : AllocId) :
    (RetagEntry.updatedMemory memory id entry tree).getAllocInfo query = memory.getAllocInfo query := by
  by_cases same : query = id
  · subst query
    have found : (RetagEntry.updatedMemory memory id entry tree).live.find? (fun row => row.1 == id) =
        some (id, {entry with allocation := entry.allocation.setExtra tree}) := MemoryCopyBridge.live_lookup_replaced _ _ _
    simp only [MemoryState.getAllocInfo, found, live]
    rfl
  · have lookup := CurrentCallOtherAllocationWindow.lookup memory.live id query
      {entry with allocation := entry.allocation.setExtra tree} (Ne.symm same)
    change (RetagEntry.updatedMemory memory id entry tree).live.find? (fun row => row.1 == query) = _ at lookup
    simp only [MemoryState.getAllocInfo, lookup]
    rfl

private theorem replace_ids {α : Type} (rows : Array (AllocId × α)) (id : AllocId) (entry : α)
    (ids : (rows.toList.map Prod.fst).Nodup) :
    (((rows.filter (fun row => row.1 != id)).push (id, entry)).toList.map Prod.fst).Nodup := by
  rw [Array.toList_push, Array.toList_filter, List.map_append]
  have kept : ((rows.toList.filter (fun row => row.1 != id)).map Prod.fst).Nodup := by
    simpa only [List.Nodup, List.filter_map, Function.comp_def] using ids.filter (fun key => key != id)
  apply List.nodup_append.mpr
  refine ⟨kept, by simp, ?_⟩
  intro key member other singleton equal
  have otherEq : other = id := by simpa using singleton
  subst other
  subst key
  obtain ⟨row, rowMember, rowId⟩ := List.mem_map.mp member
  have different := (List.mem_filter.mp rowMember).2
  simp only [rowId, bne_self_eq_false, Bool.false_eq_true] at different

private theorem repack {post : RootState} {frames : Array CompilerFrameContext.ActualFrame}
    {frame : CompilerFrameContext.ActualFrame} {machine : Before}
    (stackEq : post.stack = (Storage.withCurrent frames frame machine).stack) :
    post = Storage.withCurrent frames frame post.machine := by
  cases post with
  | mk stackMachine machine =>
    change stackMachine = _ at stackEq
    cases stackEq
    rfl

private theorem model_move {options remaining span before after tracker}
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (user : after.user = before.user) (threads : after.threads = before.threads)
    (race : after.dataRace = before.dataRace) (tracked : after.borrowTracker = some tracker)
    (mode : tracker.retagMode = .Default) : DuplicatePrefixCallModel.Model options remaining span after := by
  exact ⟨model.debugOff, model.preciseOff, model.implicitOff, user ▸ model.ghostOff, user ▸ model.shallow,
    ⟨tracker, tracked, mode⟩, race.trans model.noDataRace, user ▸ model.noBackend, user ▸ model.metadata,
    threads ▸ model.fixedScheduler, user ▸ model.unchecked, user ▸ model.noGc, model.nullComparator, model.sourceMatches⟩

theorem invoke {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (family : Family) (offset capacity : UInt64)
    (positive : 0 < len.toNat) (fits : len.toNat < 9223372036854775808)
    (encoding : argument = .pointer family.value) (assigned : input.assignment.Binds input.sourceOccurrence family)
    (charge : CurrentCallPointwiseSpatialCover.ExactCharge input.Fs input.sourceOwner .mut family.allocation offset.toNat len.toNat)
    (selected : SelectedPointer before input.tracker family offset capacity)
    (liveRole : LiveRole before input.tracker family offset len capacity true)
    (sourceReady : (∃ entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row => row.1 == family.allocation) = some (family.allocation, entry)) →
      CurrentCallBoolProtection.WindowReady before family.allocation offset.toNat len.toNat)
    (latent : LatentRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  obtain ⟨context, role, entry, doneFrame, S, familyEq, sourceReadyNow, assignedNow, scopedCopy, oldLive,
    entryEq, sourceFamily, sourceTag, sourceAllocation, frameBorrow, sourceLeaf, sourceNodes, sourceCounter, doneEq, rawCopy⟩ :=
    CurrentCallOrdinaryLiveSource.copy input family offset capacity positive fits encoding assigned charge selected liveRole sourceReady
  let prepared := CurrentCallPush.preparedMachine before #[]
  let root := CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let fresh := (live_current_rule ".CurrentCallOrdinaryLiveSource.fresh") input
  let output := CurrentCallSpatialEntryRead.output role {} fresh (UInt64.ofNat offset.toNat) len
  let sourceMachine := CurrentCallSpatialSourceInstall.copiedMachine role {} fresh (UInt64.ofNat offset.toNat) len entry
  let sourceFnMachine := CurrentCallTypedSourceCopy.validated prepared input.tracker fresh role.backing.id entry output.child.tree
  let sourceTracker : MachineHooks.BorrowState := ⟨output.global, input.tracker.retagMode⟩
  let sourceFnTracker : MachineHooks.BorrowState := ⟨output.global, .FnEntry⟩
  let args := RootArgumentsTwo.result (CurrentCallSourceArguments.doneRoot options remaining span root {} family.value len
    family.allocation input.tracker.global.nextPointerTag) count
  let boolFrame := (atSpan args ⟨601⟩).frame
  let BF : FrameState := ({} : FrameState).addProtector family.allocation input.tracker.global.nextPointerTag
  have roleId : role.backing.id = family.allocation := role.id.symm.trans (congrArg Family.allocation familyEq)
  have sourceId : S.role.backing.id = family.allocation :=
    S.role.id.symm.trans (congrArg Family.allocation sourceFamily) |>.trans roleId
  have different : family.allocation ≠ input.returnFamily.allocation := by
    intro same
    rw [same, latent.1] at oldLive
    cases oldLive
  have sourceUser : sourceMachine.user = prepared.user := by
    change {prepared.user with payload := {prepared.user.payload with ghost := false}} = prepared.user
    have ghost : prepared.user.payload.ghost = false := input.model.ghostOff
    rw [← ghost]
  have sourceModel : DuplicatePrefixCallModel.Model options remaining span sourceMachine :=
    model_move (CurrentCallResourcePreparedEntry.model input.model #[]) sourceUser rfl rfl rfl input.defaultMode
  have sourceOrigins : DuplicatePrefixTypeCacheOrigins.Origins sourceMachine.user.payload.payload.user.types := by
    rw [sourceUser]
    exact input.cacheOrigins
  have freshB : sourceTracker.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have reserve := input.resources.tagRoom
    change output.global.nextPointerTag.value.toNat < 18446744073709551615
    rw [sourceCounter]
    omega
  have initialRootBelow (tag : BorTag) (cached : input.tracker.global.rootTag? input.returnFamily.allocation = some tag) :
      tag.value.toNat < input.tracker.global.nextPointerTag.value.toNat := by
    cases found : input.tracker.global.rootPointerTags.find? (fun row => row.1 == input.returnFamily.allocation) with
    | none => simp only [GlobalState.rootTag?, found, Option.map_none] at cached; cases cached
    | some row =>
      have same : row.2 = tag := Option.some.inj (by simpa only [GlobalState.rootTag?, found, Option.map_some] using cached)
      have below := input.resources.cachedRootsBelow row (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found))
      rw [same] at below
      exact below
  have boolAbsent : sourceMachine.memory.live.find? (fun row => row.1 == input.returnFamily.allocation) = none := by
    change ((before.memory.live.filter (fun row => row.1 != role.backing.id)).push
      (role.backing.id, {entry with allocation := entry.allocation.setExtra output.child.tree})).find? _ = none
    rw [CurrentCallOtherAllocationWindow.lookup _ _ _ _ (roleId ▸ different)]
    exact latent.1
  obtain ⟨D, dFamily, dOffset, dCurrent⟩ := CurrentCallConversionBoolPhase.from_initial
    input latent (machine := sourceMachine) (tracker := sourceTracker) (frames := #[]) (frame := boolFrame) (borrowFrame := BF)
    rfl (by rfl) freshB boolAbsent rfl rfl rfl rfl (by rfl)
    (by intro tag cached; have old := initialRootBelow tag cached; change _ < output.global.nextPointerTag.value.toNat; rw [sourceCounter]; omega)
    (by exact S.runtime.below.protectors) (by change InitialRegistryVacant before input.returnFamily.allocation; exact latent.2.2.2.1)
    sourceModel.noDataRace sourceModel.ghostOff sourceModel.noBackend
  have sourceQuery : CurrentCallConversionPlan.sourceQuery before argument len = .ok (some family.allocation) := by
    rw [encoding]
    exact CurrentCallConversionPlanAdequacy.query_of_selected before input.tracker family offset capacity len true selected (.inl liveRole) fits
  have returnQuery : CurrentCallConversionPlan.returnQuery before place = .ok (some input.returnFamily.allocation) := by
    have query := CurrentCallConversionPlanAdequacy.query_of_selected before input.tracker input.returnFamily input.returnOffset
      input.returnCapacity 1 false input.returnRepresentation (.inr latent) (by decide)
    simpa only [CurrentCallConversionPlan.returnQuery, input.returnEncoding, Pointer.withOptionalProvenance] using query
  have sourcePayload : CurrentCallConversionPlan.payload before family.allocation = none :=
    CurrentCallConversionPlan.payload_live before family.allocation entry oldLive
  have boolPayload : CurrentCallConversionPlan.payload before input.returnFamily.allocation = some D.source :=
    CurrentCallConversionPlanAdequacy.payload_of_current before _ D.source latent.1 latent.2.1 latent.2.2.1 dCurrent
  have head : CurrentCallConversionPlan.selectedPayloads before argument len place = D.source :: [] := by
    unfold CurrentCallConversionPlan.selectedPayloads CurrentCallConversionPlan.selectedRows
    rw [sourceQuery, returnQuery]
    change (CurrentCallConversionPlan.rowsFromIds before (some family.allocation) (some input.returnFamily.allocation)).map Prod.snd = [D.source]
    simp [CurrentCallConversionPlan.rowsFromIds, sourcePayload, boolPayload]
  have phaseMemory : D.registered.machine.memory = RetagEntry.updatedMemory before.memory role.backing.id entry output.child.tree := rfl
  have roleLive : before.memory.live.find? (fun row => row.1 == role.backing.id) = some (role.backing.id, entry) := by
    rw [roleId]
    exact oldLive
  have phaseInfo (id : AllocId) : D.registered.machine.memory.getAllocInfo id = before.memory.getAllocInfo id := by
    rw [phaseMemory]
    exact info_tree before.memory role.backing.id entry output.child.tree roleLive id
  have phaseCounter : D.next.global.nextPointerTag.value.toNat ≤ input.tracker.global.nextPointerTag.value.toNat + 2 := by
    have successor := GenericFunctionEntryNumerics.successor_value sourceTracker.global.nextPointerTag freshB
    change (TypedRetagEmpty.successorTag sourceTracker.global.nextPointerTag freshB).value.toNat ≤ _
    rw [successor]
    change output.global.nextPointerTag.value.toNat + 1 ≤ _
    rw [sourceCounter]
    omega
  have sourceCached : ∃ base, before.user.addresses.baseAddr.find? (fun row => row.allocId == role.backing.id) = some base := by
    obtain ⟨base, cached, _⟩ := selected
    exact ⟨⟨family.allocation, base⟩, by rw [roleId]; exact cached⟩
  let phase : CurrentCallConversionBoolPhase.FirstPhase input D := {
    infoEq := phaseInfo, addresses := rfl, tape := rfl, thread := rfl, roots := by intro id; rfl,
    spent := 2, reserve := 14, room := by decide, positive := by decide, counter := phaseCounter,
    metadata := by
      intro id member
      exact CurrentCallConversionTargetMetadataFrame.transport before D.registered.machine role.backing.id
        {entry with allocation := entry.allocation.setExtra output.child.tree} (by rfl) sourceCached (by intros; assumption)
        id (CurrentCallOrdinaryConversionSelected.targets_metadata input id member),
    rest := [], head := head }
  obtain ⟨retagCtx⟩ := ActualRetagContext.exists_context options (remaining + 1) span input.model.preciseOff input.model.implicitOff
  obtain ⟨externStatic, wiring, finalAddresses, finalTape, result, ⟨protectedOutput⟩⟩ :=
    CurrentCallConversionBoolPhase.first input retagCtx D phase
  let finalMachine := protectedOutput.post.machine
  let next : MachineHooks.BorrowState := {D.next with global := result.global}
  let R := protectedOutput.output
  have postLive := CurrentCallConversionBoolFacts.live D externStatic _ _ _ _ _ result protectedOutput
  have postAddresses := CurrentCallConversionBoolFacts.addresses D externStatic _ _ _ _ _ result protectedOutput
  have postExtras := CurrentCallConversionBoolFacts.extras D externStatic _ _ _ _ _ result protectedOutput
  have postModel := CurrentCallConversionBoolFacts.model D externStatic _ _ _ _ _ result protectedOutput sourceModel input.defaultMode
  have postOrigins := CurrentCallConversionBoolFacts.origins D externStatic _ _ _ _ _ result protectedOutput sourceOrigins
  have postThreads := CurrentCallConversionBoolFacts.threads D externStatic _ _ _ _ _ result protectedOutput
  have boolDifferent : D.family.allocation ≠ S.role.backing.id := by
    rw [dFamily, sourceId]
    exact Ne.symm different
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
      exact result.bases _ _ oldCache
    · rw [S.concrete]
  have selectedRoot : next.global.rootTag? S.role.backing.id = sourceTracker.global.rootTag? S.role.backing.id := by
    let byte : AllocId × Nat := (S.role.backing.id, offset.toNat)
    have inSource : Window S.role.backing.id offset.toNat len.toNat byte := ⟨rfl, Nat.le_refl _, by dsimp [byte]; omega⟩
    obtain ⟨i, inside⟩ := S.role.covered byte inSource
    obtain ⟨rootNode, _, _, _, cachedRoot⟩ := (S.role.roles i ⟨byte, inSource, inside⟩).issued.capability.rootNode
    have newRoot : result.global.rootTag? S.role.backing.id = some rootNode.tag := result.roots _ _ cachedRoot
    exact newRoot.trans cachedRoot.symm
  have selectedExtras : finalMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == S.role.backing.id) =
      sourceMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == S.role.backing.id) := by
    rw [postExtras, CurrentCallOtherAllocationWindow.lookup _ _ _ _ boolDifferent]
  obtain ⟨current, copyReady, currentFamily, currentId, currentAllocation, _, currentTag, currentGrant, currentNode, _⟩ :=
    CurrentCallOtherBoolSourceCheckpoint.at_post S sourceReadyNow BF D.family.allocation freshB finalMachine next
      postPresent postBinding selectedRoot result.flags result.counter selectedExtras
  have currentIdOld : current.role.backing.id = family.allocation := currentId.trans sourceId
  have currentTagOld : current.tag = input.tracker.global.nextPointerTag := currentTag.trans sourceTag
  have currentPointer : current.role.family.value = CurrentCallTypedFnEntry.changedPointer family.value current.role.backing.id current.tag := by
    rw [currentFamily, sourceFamily, currentIdOld, currentTagOld]
    change CurrentCallTypedFnEntry.changedPointer role.family.value role.backing.id output.tag = _
    rw [familyEq, roleId]
    rfl
  have tagsDifferent : current.tag ≠ R.node.tag := by
    rw [currentTagOld, protectedOutput.tag]
    intro equal
    have numeric := congrArg (fun tag : BorTag => tag.value.toNat) equal
    change input.tracker.global.nextPointerTag.value.toNat = output.global.nextPointerTag.value.toNat at numeric
    rw [sourceCounter] at numeric
    omega
  have rootOld : input.tracker.global.rootTag? input.returnFamily.allocation = some D.root := by
    have cached : input.tracker.global.rootTag? D.family.allocation = some D.root := D.rootCached
    simpa only [dFamily] using cached
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
    replace_ids before.memory.live role.backing.id {entry with allocation := entry.allocation.setExtra output.child.tree} input.runtime.allocationIds
  have ids : (finalMachine.memory.live.toList.map Prod.fst).Nodup := by
    rw [postLive]
    exact replace_ids sourceMachine.memory.live D.family.allocation ⟨.machine .global, R.window.allocation⟩ sourceIds
  have tags : next.global.nextPointerTag.value.toNat + 6 < 18446744073709551615 := by
    have budget := result.rootBudget
    change result.global.nextPointerTag.value.toNat + _ + 14 < 2^64 at budget
    change result.global.nextPointerTag.value.toNat + 6 < 18446744073709551615
    omega
  have protectionBudget : (ExecutionMachine.callHooks (config options (remaining + 1) span) limits).protectArgument () place
      (Storage.withCurrent #[] boolFrame sourceMachine) = .ok () protectedOutput.post := by
    change TypedRetag.protectInPlaceFunctionArgument (config options (remaining + 1) span).retag limits.retag place _ = _
    exact (congrFun (CurrentCallBoolRetagBudget.protect options (remaining + 1) span retagCtx place input.returnLayout
      options.limits.retag limits.retag) _).symm.trans protectedOutput.actual
  have repack : protectedOutput.post = Storage.withCurrent #[]
      (registeredFrame boolFrame BF D.family.allocation sourceTracker.global.nextPointerTag) finalMachine := by
    exact repack protectedOutput.stack
  rw [repack] at protectionBudget
  have copyFinal :
      (ExecutionMachine.callHooks (config options (remaining + 1) span) limits).copyAllowTransmute ()
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span family.value len).imm, ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace 0 (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
        (Storage.withCurrent #[] (firstLive root).frame (ScopedFrame.entered prepared input.tracker .FnEntry)) =
        .ok () (Storage.withCurrent #[] (CurrentCallSourceArguments.doneRoot options remaining span root {} family.value len
          current.role.backing.id current.tag).frame sourceFnMachine) := by
    simpa only [currentIdOld, currentTagOld, doneEq] using rawCopy
  have protectionFinal :
      (ExecutionMachine.callHooks (config options (remaining + 1) span) limits).protectArgument () place
        (Storage.withCurrent #[] (atSpan (RootArgumentsTwo.result (CurrentCallSourceArguments.doneRoot options remaining span root {}
          family.value len current.role.backing.id current.tag) count) ⟨601⟩).frame sourceMachine) =
        .ok () (Storage.withCurrent #[] (registeredFrame (atSpan (RootArgumentsTwo.result
          (CurrentCallSourceArguments.doneRoot options remaining span root {} family.value len current.role.backing.id current.tag) count) ⟨601⟩).frame
          (({} : FrameState).addProtector current.role.backing.id current.tag) R.id R.node.tag) finalMachine) := by
    simpa only [currentIdOld, currentTagOld, R, boolFrame, args, BF, protectedOutput.id, protectedOutput.tag] using protectionBudget
  exact CurrentCallOrdinaryPositiveFinish.invoke input family.value encoding count sourceMachine sourceFnMachine finalMachine
    sourceFnTracker next offset.toNat current copyReady R currentPointer rfl rfl sourceModel.shallow rfl copyFinal protectionFinal
    protectedOutput.tracked input.defaultMode postModel postOrigins tagsDifferent (fun _ => absent)
    (by intro same; have idEq := protectedOutput.id; rw [dFamily] at idEq; exact False.elim (different (currentIdOld.symm.trans same.symm |>.trans idEq)))
    ids tags (postThreads.trans rfl)

end
end DuplicatePrefix.CurrentCallOrdinaryLiveCurrentSafety

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryLiveCurrentSafety.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved LIVE/CURRENT Result dependency {name}: {dependency}"
