import duplicate_prefix.CurrentCallOrdinaryCurrentSource
import duplicate_prefix.CurrentCallOrdinaryLiveCurrentSafety
import duplicate_prefix.CurrentCallOrdinaryReturnLive
import duplicate_prefix.CurrentCallLiveBoolTransport
import duplicate_prefix.CurrentCallConversionSourceAfterBool
import duplicate_prefix.CurrentCallConversionBoolModel
import duplicate_prefix.CurrentCallSelectedKeyOrigin

/-! The CURRENT-source / LIVE-return branch executes its original source
conversion, preserves the selected Bool, and reuses the common continuation. -/
namespace DuplicatePrefix.CurrentCallOrdinaryCurrentLiveSafety
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
elab "current_live_rule " suffix:str : term => do
  let found := (← getEnv).constants.toList.filter (fun (name, _) => name.toString.endsWith suffix.getString)
  match found with
  | [(name, _)] => return mkConst name
  | _ => throwError "expected one checked CURRENT/LIVE theorem {suffix.getString}"

set_option linter.unusedVariables false in
theorem invoke {options limits remaining span before argument len place}
    (input : OrdinaryInput options limits remaining span before argument len place)
    (family : Family) (offset capacity : UInt64)
    (positive : 0 < len.toNat) (fits : len.toNat < 9223372036854775808)
    (encoding : argument = .pointer family.value) (assigned : input.assignment.Binds input.sourceOccurrence family)
    (charge : CurrentCallPointwiseSpatialCover.ExactCharge input.Fs input.sourceOwner .mut family.allocation offset.toNat len.toNat)
    (selected : SelectedPointer before input.tracker family offset capacity)
    (latent : LatentRole before input.tracker family offset len capacity true)
    (sourceReady : (∃ entry : LocalAllocation Provenance BorrowTree MiriMemoryKind,
      before.memory.live.find? (fun row => row.1 == family.allocation) = some (family.allocation, entry)) →
      CurrentCallBoolProtection.WindowReady before family.allocation offset.toNat len.toNat)
    (liveReturn : LiveRole before input.tracker input.returnFamily input.returnOffset 1 input.returnCapacity false)
    (count : UInt64) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before argument len count place := by
  obtain ⟨absent, noFunction, noVaList, registry, ⟨rootTag, concrete, cachedRoot⟩,
    image, currentImage, size, compiler, physical⟩ := latent
  obtain ⟨base, cachedBase, addressRoom, address, nonnull, represented⟩ := selected
  have sumBound : base.toNat + offset.toNat < 2^64 := by
    have bounds := physical.2.2.1
    rw [size] at bounds
    change offset.toNat + len.toNat ≤ capacity.toNat at bounds
    omega
  have bits : family.value.offset.bytes = base + offset := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt sumBound]
    exact address
  have value : family.value = Pointer.new (.concrete family.allocation rootTag) (Size.ofBytes (base + offset)) := by
    cases equal : family.value with
    | mk position provenance =>
      simp only [equal] at concrete bits
      cases position
      simp only [Pointer.new, Size.ofBytes]
      simp_all
  have encoding' : argument = .pointer (Pointer.new (.concrete family.allocation rootTag) (Size.ofBytes (base + offset))) :=
    encoding.trans (congrArg DuplicatePrefixSliceArgument.Argument.pointer value)
  obtain ⟨rest, externStatic, finalAddresses, finalTape, result, doneFrame, wiring, head, rawCopy, scopedCopy,
    frameBorrow, frameSize, doneEq, stage, S, copyReady, sourceId, sourcePointer, sourceAllocation,
    sourceGrant, sourceTag, sourceLeaf, sourceNodes, sourceModel, sourceOrigins, sourceThreads, sourceMemory, sourceTracked, sourceShallow⟩ :=
    CurrentCallOrdinaryCurrentSource.copy family.allocation rootTag base offset input encoding' image currentImage absent
      noFunction noVaList registry cachedRoot cachedBase (by rw [← bits]; exact nonnull) positive fits physical.2.2.1 physical
      (by rw [size]; exact addressRoom)
  let prepared := CurrentCallPush.preparedMachine before #[]
  let root := CurrentCallSpatialEntryControl.root before #[] place input.model.noDataRace
  let ptr : Pointer Provenance := Pointer.new (.concrete family.allocation rootTag) (Size.ofBytes (base + offset))
  let fresh := (current_live_rule ".CurrentCallOrdinaryCurrentSource.fresh") input
  let sourceFnMachine := CurrentCallOrdinaryCurrentSource.rawPost options result.machine family.allocation rootTag
    input.tracker.global.nextPointerTag result.converted result.global.protectedTags offset len
  let sourceMachine := {sourceFnMachine with borrowTracker := some ⟨result.global, input.tracker.retagMode⟩}
  let sourceTracker : MachineHooks.BorrowState := ⟨result.global, input.tracker.retagMode⟩
  let args := RootArgumentsTwo.result (CurrentCallSourceArguments.doneRoot options remaining span root {} ptr len
    family.allocation input.tracker.global.nextPointerTag) count
  let boolFrame := (atSpan args ⟨601⟩).frame
  let BF : FrameState := ({} : FrameState).addProtector family.allocation input.tracker.global.nextPointerTag
  obtain ⟨B⟩ := CurrentCallOrdinaryReturnLive.form input liveReturn
  have different : family.allocation ≠ B.physical.id := by
    intro same
    have old := B.physical.live
    rw [← same, absent] at old
    cases old
  let W := CurrentCallResourceFnEntry.registered_window B.B B.runtime {} fresh
  obtain ⟨wAllocation, wPrecise, wPointer⟩ :=
    (current_live_rule ".CurrentCallSpatialEntryRead.registered_window_fields") B.B B.runtime {} fresh
  have wRuntime := (GeneralBorrowFnEntryRegistrationRuntime.prepare B.B.allocation.extra input.tracker.global {}
    B.physical.id fresh B.runtime).2.2.2.1
  have sourceAddresses : sourceMachine.user.addresses = result.addresses := by
    change result.machine.user.addresses = result.addresses
    rw [result.frame, CurrentCallConversionFiniteFold.state_eq]
  have live : sourceMachine.memory.live.find? (fun row => row.1 == B.physical.id) =
      before.memory.live.find? (fun row => row.1 == B.physical.id) := by
    change sourceFnMachine.memory.live.find? _ = _
    rw [sourceMemory, CurrentCallOtherAllocationWindow.lookup _ _ _ _ different]
  have roots : ∀ tag, ({input.tracker with global :=
      (GeneralBorrowFnEntryRegistration.registered input.tracker.global {} B.physical.id fresh).1}).global.rootTag? B.physical.id = some tag →
      sourceTracker.global.rootTag? B.physical.id = some tag := by
    intro tag cached
    exact result.roots _ _ cached
  have baseHit : sourceMachine.user.addresses.baseAddr.find? (fun row => row.allocId == B.physical.id) =
      before.user.addresses.baseAddr.find? (fun row => row.allocId == B.physical.id) := by
    rw [sourceAddresses]
    exact (result.bases _ _ B.physical.cachedBase).trans B.physical.cachedBase.symm
  have extrasRows : sourceMachine.user.payload.payload.user.runtime.extras.allocations =
      (before.user.payload.payload.user.runtime.extras.allocations.filter (fun row => row.1 != family.allocation)).push
        (family.allocation, ⟨none, #[]⟩) := by
    change (result.machine.user.payload.payload.user.runtime.extras.allocations.filter (fun row => row.1 != family.allocation)).push
      (family.allocation, ⟨none, #[]⟩) = _
    rw [result.frame, CurrentCallConversionFiniteFold.state_eq]
    rfl
  have extras : sourceMachine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == B.physical.id) =
      before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == B.physical.id) := by
    rw [extrasRows, CurrentCallOtherAllocationWindow.lookup _ _ _ _ different]
  have wild : CurrentCallLiveBoolTransport.WildcardQuery sourceMachine B.physical := by
    intro provenance
    have old := B.binding
    obtain ⟨entry, oldBase, oldLive, oldCached, _, _, _, _, _, represented⟩ := old
    have sameEntry : entry = B.physical.entry := (Prod.mk.inj (Option.some.inj (oldLive.symm.trans B.physical.live))).2
    have sameBase : oldBase = B.physical.base := congrArg (fun row : Miri.Memory.AllocAddresses.BaseAddressEntry => row.address)
      (Option.some.inj (oldCached.symm.trans B.physical.cachedBase))
    subst entry
    subst oldBase
    rw [provenance] at represented
    refine ⟨?_, ?_, ?_⟩
    · rw [sourceAddresses, result.provenanceMode]
      exact represented.1
    · rw [sourceAddresses, result.exposed]
      exact represented.2.1
    · rw [sourceAddresses]
      exact result.geometry _ _ _ _ (by
        change CurrentCallConversionInfoRows.sizes before.memory B.physical.id = B.physical.entry.allocation.byteSize
        apply CurrentCallConversionInfoRows.queried_size (info := ⟨B.physical.entry.allocation.byteSize, B.physical.entry.allocation.align, .liveData, B.physical.entry.allocation.mutability⟩)
        simp only [MemoryState.getAllocInfo, B.physical.live]
        rfl) represented.2.2
  obtain ⟨currentBool⟩ := CurrentCallLiveBoolTransport.transport W wRuntime B.physical rfl rfl
    (B.allocation.trans wAllocation.symm) B.binding B.ready sourceMachine sourceTracker live result.flags result.counter roots baseHit extras wild
  let physical : CandidateCurrentBoolUninitWrite.PhysicalWindow sourceMachine place := {B.physical with
    live := live.trans B.physical.live, cachedBase := baseHit.trans B.physical.cachedBase}
  have bPointer : physical.pointer = currentBool.window.pointer.value :=
    B.pointer.trans (congrArg PointerInstance.value (currentBool.pointer.trans wPointer)).symm
  have bAllocation : physical.entry.allocation = currentBool.window.allocation :=
    B.allocation.trans (currentBool.allocation.trans wAllocation).symm
  have bBinding : CandidateCallBindings.WindowBinding sourceMachine physical.pointer physical.id physical.offset.toNat 1 := by
    simpa only [currentBool.physicalPointer, currentBool.physicalId, currentBool.physicalOffset] using currentBool.binding
  have bReady : CurrentCallBoolProtection.WindowReady sourceMachine physical.id physical.offset.toNat 1 := by
    simpa only [currentBool.physicalId, currentBool.physicalOffset] using currentBool.ready
  have bDistinct : currentBool.window.allocation.extra.roots.toList.Nodup := by
    rw [currentBool.allocation, wAllocation]
    exact B.distinct
  have bShort : currentBool.window.allocation.extra.nodes.size + 1 < 65536 := by
    rw [currentBool.allocation, wAllocation]
    exact B.nodeRoom
  have freshB : sourceTracker.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    have budget := result.rootBudget
    change result.global.nextPointerTag.value.toNat + _ + 15 < 2^64 at budget
    change result.global.nextPointerTag.value.toNat < 18446744073709551615
    omega
  let sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind :=
    ⟨.machine .global, result.converted.mapExtra (fun _ => stage.output.child.tree)⟩
  have sourceLive : sourceMachine.memory.live.find? (fun row => row.1 == S.role.backing.id) =
      some (S.role.backing.id, sourceEntry) := by
    rw [sourceId]
    change sourceFnMachine.memory.live.find? _ = _
    rw [sourceMemory]
    exact MemoryCopyBridge.live_lookup_replaced before.memory family.allocation sourceEntry
  have sourceAlloc : sourceEntry.allocation = S.role.backing.allocation := sourceAllocation.symm
  have sourceDifferent : S.role.backing.id ≠ physical.id := by
    rw [sourceId]
    exact different
  have separated : ∀ byte, Window S.role.backing.id offset.toNat len.toNat byte →
      Window physical.id physical.offset.toNat 1 byte → False := by
    intro byte src dst
    exact sourceDifferent (src.1.symm.trans dst.1)
  obtain ⟨ctx⟩ := ActualRetagContext.exists_context options (remaining + 1) span input.model.preciseOff input.model.implicitOff
  obtain ⟨output, post, R, currentSource, protect, currentReady, currentFamily, currentId, currentTag, currentGrant,
    returnId, returnOffset, original, tracked, globalEq, stackEq, returnTag, growth, operation, tagsEq, extra, mutation, postEq⟩ :=
    CurrentCallConversionSourceAfterBool.after_protect_live options (remaining + 1) span ctx sourceMachine sourceTracker
      offset.toNat len S copyReady sourceEntry sourceLive sourceAlloc sourceLeaf sourceNodes B.data 0 #[] boolFrame BF rfl (by rfl)
      place physical currentBool.window bPointer bAllocation currentBool.runtime bBinding bDistinct freshB bShort
      (by intro same; exact False.elim (sourceDifferent same)) separated sourceModel.ghostOff sourceModel.noDataRace sourceModel.noBackend bReady
  let L : CurrentCallConversionBoolPhase.LiveData sourceMachine sourceTracker boolFrame BF place := {
    data := B.data, owner := 0, physical := physical, window := currentBool.window, enabled := rfl, frameBorrow := by rfl,
    pointer := bPointer, allocation := bAllocation, runtime := currentBool.runtime, binding := bBinding,
    distinct := bDistinct, fresh := freshB, short := bShort, ghost := sourceModel.ghostOff, race := sourceModel.noDataRace,
    backend := sourceModel.noBackend, ready := bReady }
  let O : CurrentCallConversionBoolPhase.LiveProtected (options := options) (remaining := remaining + 1) (span := span) L #[] := {
    operation := output, post := post, output := R, actual := protect, id := returnId, offset := returnOffset,
    original := original, tag := returnTag, nodes := growth, tracked := tracked, global := globalEq, stack := stackEq,
    raw := operation, machineEq := postEq, tagMapping := tagsEq, extra := extra, write := mutation }
  have postModel := CurrentCallConversionBoolModel.live_model O sourceModel
  have postOrigins := CurrentCallConversionBoolModel.live_origins O sourceOrigins
  have postThreads := CurrentCallConversionBoolModel.live_threads O
  have currentIdOld : currentSource.role.backing.id = family.allocation := currentId.trans sourceId
  have currentTagOld : currentSource.tag = input.tracker.global.nextPointerTag := currentTag.trans sourceTag
  have currentPointer : currentSource.role.family.value = CurrentCallTypedFnEntry.changedPointer ptr currentSource.role.backing.id currentSource.tag := by
    rw [currentFamily, sourcePointer, currentIdOld, currentTagOld]
    rfl
  have later : currentSource.tag.value < sourceTracker.global.nextPointerTag.value := by
    rw [currentTag]
    have older := GeneralBorrowParentTagInvariant.parent_below_fresh S.role.backing.allocation.extra sourceTracker.global S.runtime
      S.grant S.node S.nodeAt
    rw [S.nodeTag] at older
    exact older
  have tagsDifferent : currentSource.tag ≠ R.node.tag := by
    rw [returnTag]
    intro equal
    rw [equal] at later
    exact UInt64.lt_irrefl _ later
  have bBounds : physical.offset.toNat + (1 : UInt64).toNat ≤ currentBool.window.allocation.extra.locations.size.bytes.toNat := by
    rw [currentBool.window.issued.capability.treeExtent, ← bAllocation, physical.size]
    exact physical.bounds
  have origins := CurrentCallSelectedKeyOrigin.operation currentBool.window currentBool.runtime BF freshB rfl bDistinct
    (by omega) (by omega) physical.offset 1 rfl rfl (by decide) bBounds output operation
  have oldBelow : ∀ key index, (key, index) ∈ currentBool.window.allocation.extra.tagMapping.mapping → key.value < currentSource.tag.value := by
    intro key index member
    rw [currentBool.allocation, wAllocation] at member
    rw [currentTagOld]
    exact UInt64.lt_iff_toNat_lt.mpr (B.runtime.below.mapping (key, index) member)
  have absent : ∀ index node, R.window.allocation.extra.nodes.get index = some node → node.tag ≠ currentSource.tag := by
    apply CurrentCallSelectedKeyOrigin.node_absent currentBool.window.allocation.extra R.window.allocation.extra output.global
      currentSource.tag sourceTracker.global.nextPointerTag
    · intro key index member
      rw [tagsEq] at member
      exact origins key index member
    · exact oldBelow
    · exact later
    · exact R.runtime
  have sourceIds : (sourceMachine.memory.live.toList.map Prod.fst).Nodup := by
    change (sourceFnMachine.memory.live.toList.map Prod.fst).Nodup
    rw [sourceMemory]
    exact (current_live_rule ".CurrentCallOrdinaryLiveCurrentSafety.replace_ids") before.memory.live family.allocation sourceEntry input.runtime.allocationIds
  have postLive : post.machine.memory.live = (sourceMachine.memory.live.filter (fun row => row.1 != physical.id)).push
      (physical.id, {physical.entry with allocation := R.window.allocation}) := by
    have actual := congrArg (fun machine : Before => machine.memory.live) postEq
    simpa only [ReturnProtection.borrowedState, RetagEntry.updatedMemory, Storage.withCurrent,
      current_live_rule ".CurrentCallConversionBoolFacts.replace_twice"] using actual
  have ids : (post.machine.memory.live.toList.map Prod.fst).Nodup := by
    rw [postLive]
    exact (current_live_rule ".CurrentCallOrdinaryLiveCurrentSafety.replace_ids") sourceMachine.memory.live physical.id
      {physical.entry with allocation := R.window.allocation} sourceIds
  have tags : output.global.nextPointerTag.value.toNat + 6 < 18446744073709551615 := by
    have budget := result.rootBudget
    change result.global.nextPointerTag.value.toNat + _ + 15 < 2^64 at budget
    rw [globalEq]
    change (TypedRetagEmpty.successorTag sourceTracker.global.nextPointerTag freshB).value.toNat + 6 < _
    rw [GenericFunctionEntryNumerics.successor_value]
    change result.global.nextPointerTag.value.toNat + 1 + 6 < _
    omega
  have protectionBudget : (ExecutionMachine.callHooks (config options (remaining + 1) span) limits).protectArgument () place
      (Storage.withCurrent #[] boolFrame sourceMachine) = .ok () post := by
    change TypedRetag.protectInPlaceFunctionArgument (config options (remaining + 1) span).retag limits.retag place _ = _
    exact (congrFun (CurrentCallBoolRetagBudget.protect options (remaining + 1) span ctx place input.returnLayout
      options.limits.retag limits.retag) _).symm.trans protect
  have repack : post = Storage.withCurrent #[] (registeredFrame boolFrame BF physical.id sourceTracker.global.nextPointerTag) post.machine :=
    (current_live_rule ".CurrentCallOrdinaryLiveCurrentSafety.repack") stackEq
  rw [repack] at protectionBudget
  have doneFrameEq : doneFrame = (CurrentCallSourceArguments.doneRoot options remaining span root {} ptr len family.allocation input.tracker.global.nextPointerTag).frame := doneEq
  have copyFinal :
      (ExecutionMachine.callHooks (config options (remaining + 1) span) limits).copyAllowTransmute ()
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span ptr len).imm, ActualReferenceMetadata.reference⟩
        (LocalPlaces.localRuntimePlace 0 (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
        (Storage.withCurrent #[] (firstLive root).frame (ScopedFrame.entered prepared input.tracker .FnEntry)) =
        .ok () (Storage.withCurrent #[] (CurrentCallSourceArguments.doneRoot options remaining span root {} ptr len
          currentSource.role.backing.id currentSource.tag).frame sourceFnMachine) := by
    simpa only [currentIdOld, currentTagOld, doneFrameEq] using rawCopy
  have protectionFinal :
      (ExecutionMachine.callHooks (config options (remaining + 1) span) limits).protectArgument () place
        (Storage.withCurrent #[] (atSpan (RootArgumentsTwo.result (CurrentCallSourceArguments.doneRoot options remaining span root {}
          ptr len currentSource.role.backing.id currentSource.tag) count) ⟨601⟩).frame sourceMachine) =
        .ok () (Storage.withCurrent #[] (registeredFrame (atSpan (RootArgumentsTwo.result
          (CurrentCallSourceArguments.doneRoot options remaining span root {} ptr len currentSource.role.backing.id currentSource.tag) count) ⟨601⟩).frame
          (({} : FrameState).addProtector currentSource.role.backing.id currentSource.tag) R.id R.node.tag) post.machine) := by
    simpa only [currentIdOld, currentTagOld, returnId, returnTag, boolFrame, args, BF] using protectionBudget
  exact CurrentCallOrdinaryPositiveFinish.invoke input ptr encoding' count sourceMachine sourceFnMachine post.machine
    ⟨result.global, .FnEntry⟩ ⟨output.global, input.tracker.retagMode⟩ offset.toNat currentSource currentReady R currentPointer
    sourceTracked rfl sourceShallow rfl copyFinal protectionFinal tracked input.defaultMode postModel postOrigins tagsDifferent (fun _ => absent)
    (by intro same; exact False.elim (different (currentIdOld.symm.trans same.symm |>.trans returnId)))
    ids tags (postThreads.trans sourceThreads)

end
end DuplicatePrefix.CurrentCallOrdinaryCurrentLiveSafety

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallOrdinaryCurrentLiveSafety.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved CURRENT/LIVE Result dependency {name}: {dependency}"
