import duplicate_prefix.S02WildcardReturnSameCountEntry
import duplicate_prefix.S02SameDestinationUninitInitializedWrite
import duplicate_prefix.S02SameDestinationUninitInitializedBits
namespace DuplicatePrefix.S02WildcardReturnSameAcceptedPhysical
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
private theorem scoped_write
    {options : EvalConfigurationCore.Options} {remaining : Nat}
    (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance)
    (input : DuplicatePrefixReturnPlaceInput.Input state.machine place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (short : input.entry.allocation.extra.nodes.size < 65536)
    (tag : BorTag) (child : UniIndex)
    (tagged : input.entry.allocation.extra.indexOfTag tag = some child)
    (positive : GeneralBorrowFreshRootScopedRow.Positive input.entry.allocation.extra input.tracker.global.protectedTags
      child child tag input.offset 1)
    (concrete : input.pointer.provenance = .concrete input.id tag)
    (race : state.machine.dataRace = none)
    (backend : state.machine.user.payload.payload.user.backend = .none)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : state.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat + 1 ≤ row.1.bytes.toNat) :
    ∃ updated, PlaceMachine.writeMemory (config options remaining span).access (fun _ => false) .uninit place state =
      .ok () {state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun row => row.1 != input.id).push
          (input.id,{input.entry with allocation := updated}))}}} ∧
      input.entry.allocation.initializationMask.setRange (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) false = .ok updated.initializationMask ∧
      ProvenanceMap.clear (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) (AllocationCopy.snapshot input.entry.allocation)
        (Size.ofBytes 8) input.entry.allocation.provenanceMap = .ok () updated.provenanceMap := by
  let contexts := DuplicatePrefixPhysicalContexts.canonical options remaining span
  let context := contexts.validationContext
  have runtimeWidth : context.access.runtime.base.pointerWidth = .w64 := by
    rw [←contexts.accessEq]
    exact CanonicalConfigFacts.actual_target_width options () remaining span
  let borrowed := input.entry.allocation.extra.performBorrowAccessRange (.concrete tag)
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write input.tracker.global.protectedTags
    .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,afterPositive⟩ := GeneralBorrowFreshRootScopedRange.access_runtime_kind
    input.entry.allocation.extra input.tracker.global runtime tag child child tag tagged
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write .VisitChildrenOfAccessed input.offset 1 positive
    distinct short (Nat.le_refl _) (Nat.le_refl _)
  have present : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,sync⟩) := extras
  have syncDone := S04ReturnSyncOutside.sync_access_outside context.extras state.machine input.id
    (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) true ⟨none,sync⟩ present outside
  have actual := S04ReturnExtrasAccess.source_write_access_exact context.prepared context.image
    context.maximum context.fuel context.globalHooks context.pointers context.extras state.machine input.tracker
    input.entry.allocation.extra input.id (.concrete tag) (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1))
    sync race backend input.enabled present
  have access : PlaceMachine.memoryAccess context.access true ⟨state.machine,none⟩ input.entry.allocation.extra
      input.id (.concrete tag) (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) =
      ⟨⟨state.machine,none⟩,borrowed.tree,.ok ()⟩ := by
    change PlaceMachine.memoryAccess context.access true _ _ _ _ _ = _ at actual
    dsimp only [allocRange] at actual syncDone ⊢
    simp only [contract.completed,syncDone] at actual
    exact actual
  have resolved : context.access.resolvePointer state.machine.memory
      input.pointer.withOptionalProvenance (Int.ofNat (1 : UInt64).toNat) state.machine =
      .ok (.ok ⟨input.id,Size.ofBytes input.offset,S04ReturnBorrowBridge.extra input.pointer.provenance⟩) state.machine := by
    have off : input.pointer.offset = Size.ofBytes (input.base + input.offset) := by
      cases h : input.pointer.offset
      simpa [h,Size.ofBytes] using congrArg Size.ofBytes input.pointerAddress
    rw [show context.access.resolvePointer = TypedMemoryProviders.resolvePointer context.pointers from rfl]
    have res := MemoryCopyBridge.typed_resolve_cached context.pointers state.machine.memory state.machine
      input.id tag input.base input.offset (Int.ofNat (1 : UInt64).toNat) contexts.validationWidth
      (by decide) (by decide) input.cachedBase
    simpa only [Pointer.withOptionalProvenance,concrete,off,Pointer.new,S04ReturnBorrowBridge.extra] using res
  have access' : PlaceMachine.memoryAccess context.access true ⟨state.machine,none⟩ input.entry.allocation.extra
      input.id (S04ReturnBorrowBridge.extra input.pointer.provenance)
      (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) =
      ⟨⟨state.machine,none⟩,borrowed.tree,.ok ()⟩ := by
    simpa only [concrete,S04ReturnBorrowBridge.extra] using access
  obtain ⟨updated,write,maskEq,extra,bytes,length,mutable,maskWf,maskLen,provenanceClear⟩ := S02SameDestinationUninitInitializedWrite.on_context_of_access
    context state place input _ contexts.validationWidth runtimeWidth contexts.validationRuntimeSize access' resolved (fun _ => false)
  exact ⟨updated,by simpa only [contexts.accessEq] using write,maskEq,provenanceClear⟩
/-- Physical initialization and provenance equations for the SAME allocation
witness installed by the actual wildcard protection. Initial source bytes and
disjointness are current storage facts, never a future initialization gate. -/
theorem of_packet
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615) (wildcard : input.pointer.provenance = .wildcard)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (owned : FrameState)
    (frameBorrow : frame.extra.borrowTracker = some owned)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) = some (input.id,⟨none,sync⟩))
    (outsideSync : ∀ row ∈ sync,row.1.bytes.toNat < input.offset.toNat ∨ input.offset.toNat+1 ≤ row.1.bytes.toNat)
    (sourceTag : BorTag) (query selected : UniIndex) (maximum : Option BorTag) (lower width : UInt64) (node : TreeNode)
    (post : S02WildcardReturnSameCountEntry.Packet options remaining span budget before place input frames frame owned fresh sourceTag query selected maximum lower width node)
    (outside : input.offset.toNat+1 ≤ lower.toNat ∨ (lower+width).toNat ≤ input.offset.toNat)
    (initialized : InitMaskCopy.InitializedOn input.entry.allocation.initializationMask (Size.ofBytes lower) (Size.ofBytes (lower+width))) :
    input.entry.allocation.initializationMask.setRange (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) false = .ok post.updated.initializationMask ∧
    InitMaskCopy.InitializedOn post.updated.initializationMask (Size.ofBytes lower) (Size.ofBytes (lower+width)) ∧
    ProvenanceMap.clear (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) (AllocationCopy.snapshot input.entry.allocation)
      (Size.ofBytes 8) input.entry.allocation.provenanceMap = .ok () post.updated.provenanceMap := by
  obtain ⟨tree,retag,treeRuntime,capacity,short,roots,_order,_exposed,_other,child,tagged,_rootPush,⟨positive⟩,_activity,_⟩ :=
    S03ReturnWildcardProtectionRawOtherTags.retag_other_tags budget before model place input runtime distinct order headroom fresh wildcard frames frame owned frameBorrow
  let current := ReturnProtection.borrowedState frames frame owned before input.tracker fresh input.id input.entry tree
  let next := S04ReturnRetaggedInput.from_borrowed input frames frame owned fresh tree child (some child) (some input.tracker.global.nextPointerTag) tagged capacity positive.base
  obtain ⟨updated,write,maskEq,clearEq⟩ := scoped_write span current _ next treeRuntime roots short input.tracker.global.nextPointerTag child tagged positive rfl
    model.noDataRace model.noBackend sync extras outsideSync
  let after := S04ProtectUninit.finished before place input frames frame owned fresh tree updated
  have configured : (config options remaining span).retag.writeUninit (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag) current = .ok () after := by
    obtain ⟨ctx⟩ := ActualRetagContext.exists_context options remaining span model.preciseOff model.implicitOff
    rw [ctx.construction]
    change (do let access ← ValidityMachine.scopedAccess (config options remaining span).access
               PlaceMachine.writeMemory access (fun _ => false) .uninit (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag)) current = .ok () after
    have notGhost : (config options remaining span).access.ghostMode = false := by rw [(DuplicatePrefixPhysicalContexts.canonical options remaining span).accessEq];rfl
    simp only [bind,EStateM.bind,S04ProtectUninitWrite.scopedAccess_of_not_ghost (config options remaining span).access current notGhost model.ghostOff]
    exact write
  have protect : TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag budget place
      (Storage.withCurrent frames frame before) = .ok () after := by
    unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
    simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,Storage.withCurrent,input.enabled,Option.isSome_some,↓reduceIte]
    erw [retag]
    exact configured
  have sameState := (EStateM.Result.ok.inj (protect.symm.trans post.protect)).2
  dsimp only [after] at sameState
  have firstLive : after.machine.memory.live.find? (fun row => row.1 == input.id) = some (input.id,{input.entry with allocation := updated}) := MemoryCopyBridge.live_lookup_replaced _ _ _
  have secondLive : (S04ProtectUninit.finished before place input frames frame owned fresh post.tree post.updated).machine.memory.live.find? (fun row => row.1 == input.id) =
      some (input.id,{input.entry with allocation := post.updated}) := MemoryCopyBridge.live_lookup_replaced _ _ _
  have updatedEq : updated = post.updated := by
    change (S04ProtectUninit.finished before place input frames frame owned fresh tree updated).machine.memory.live.find? _ = _ at firstLive
    rw [sameState] at firstLive
    exact congrArg (fun row => row.2.allocation) (Option.some.inj (firstLive.symm.trans secondLive))
  change input.entry.allocation.initializationMask.setRange _ false = .ok updated.initializationMask at maskEq
  change ProvenanceMap.clear _ (AllocationCopy.snapshot (input.entry.allocation.setExtra tree)) _ input.entry.allocation.provenanceMap = .ok () updated.provenanceMap at clearEq
  rw [(AllocationCopy.set_extra_preserves_storage input.entry.allocation tree).2.2.2.2.2.2,updatedEq] at clearEq
  rw [updatedEq] at maskEq
  have sourceBounds := post.sourcePositive.bounds
  rw [post.capacity,input.borrowSize] at sourceBounds
  have fullFits : lower.toNat+width.toNat < 2^64 := by have := input.capacity.toNat_lt;omega
  have fullNat : (lower+width).toNat = lower.toNat+width.toNat := by rw [UInt64.toNat_add,Nat.mod_eq_of_lt fullFits]
  have endFits : input.offset.toNat+1 < 2^64 := by have := input.capacity.toNat_lt;have := input.bounds;omega
  have endNat : (input.offset+1).toNat = input.offset.toNat+1 := by rw [UInt64.toNat_add];exact Nat.mod_eq_of_lt endFits
  have endpoint := DuplicatePrefix.source_end (Size.ofBytes input.offset) 1 (by simpa [Size.ofBytes] using endFits)
  obtain ⟨mask,maskOk,_,_,preserved⟩ := S02SameDestinationUninitInitializedBits.one_byte_frame input.entry.allocation.initializationMask
    (Size.ofBytes lower) (Size.ofBytes (lower+width)) (allocRange (Size.ofBytes input.offset) (Size.ofBytes 1)) (Size.ofBytes (input.offset+1))
    input.maskValid initialized (by have := post.sourcePositive.positive;simpa [Size.ofBytes,fullNat] using (show lower.toNat < lower.toNat+width.toNat by omega))
    (by simpa [input.maskLength,Size.ofBytes,fullNat] using sourceBounds) endpoint (by simpa [Size.ofBytes,allocRange] using endNat)
    (by simpa [input.maskLength,Size.ofBytes,endNat] using input.bounds) (by simpa [Size.ofBytes,allocRange,endNat] using outside.symm)
  have sameMask : mask = post.updated.initializationMask := Except.ok.inj (maskOk.symm.trans maskEq)
  exact ⟨maskEq,sameMask ▸ preserved,clearEq⟩
end
end DuplicatePrefix.S02WildcardReturnSameAcceptedPhysical
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardReturnSameAcceptedPhysical.of_packet) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved wildcard return accepted physical dependency {dependency}"
