import duplicate_prefix.GeneralBorrowForestAsMutInvocationCore
import duplicate_prefix.GeneralBorrowForestAsMutEntryPaths
namespace DuplicatePrefix.GeneralBorrowForestAsMutInvocation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Concurrency
open PhysicalMachineWrite GeneralBorrowProjection GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option autoImplicit false in
/-- All caller, allocation, graph and borrowed-slice data precede the actual
as_mut_ptr entry; no helper-poststate or operation success is assumed. -/
structure Input where
  start : GeneralBorrowForestAsMutInvocationCore.Input
  statementFuel : start.limits.validation = start.fuel+1
  target : UniIndex
  targetNode : TreeNode
  targetPresent : start.entry.allocation.extra.nodeAt target = some targetNode
  targetNotExposed : targetNode.isExposed = false
  targetTag : BorTag
  targetNotHelper : start.tracker.global.nextPointerTag ≠ targetTag
  targetTagPresent : start.entry.allocation.extra.indexOfTag targetTag = some target
  targetRootPath : ∀ location, ((source_normal_projection start.entry.allocation.extra location start.tracker.global.protectedTags).topology.ancestorPath target.toNat).getLast! = start.data.primary.toNat
  targetWithin : GeneralBorrowFreshActiveWithin.ActiveWithin start.entry.allocation.extra target .Write start.offset (start.offset+start.len)
  subset : ∀ location : LocationTree,
    ∀ position ∈ (source_normal_projection start.entry.allocation.extra location start.tracker.global.protectedTags).topology.ancestorPath target.toNat,
      position ∈ (source_normal_projection start.entry.allocation.extra location start.tracker.global.protectedTags).topology.ancestorPath start.data.parent.toNat
  escaping : ∀ (location : LocationTree) (index : UniIndex) (node : TreeNode), start.entry.allocation.extra.nodeAt index = some node →
    index.toNat ∈ (source_normal_projection start.entry.allocation.extra location start.tracker.global.protectedTags).topology.ancestorPath start.data.parent.toNat →
    index.toNat ∉ (source_normal_projection start.entry.allocation.extra location start.tracker.global.protectedTags).topology.ancestorPath target.toNat →
    start.tracker.global.protectedTags.contains node.tag = false
  storage : start.entry.allocation.len = start.entry.allocation.byteSize.bytes.toNat
  maskValid : InitMaskCopy.WellFormed start.entry.allocation.initializationMask
  maskLength : start.entry.allocation.initializationMask.len = start.entry.allocation.byteSize
  initialized : InitMaskCopy.InitializedOn start.entry.allocation.initializationMask (Size.ofBytes start.offset) (Size.ofBytes (start.offset+start.count))
  provenance : ProvenanceCopy.WellFormed start.entry.allocation.provenanceMap start.entry.allocation.len
  storageFits : start.entry.allocation.len+64 < 18446744073709551616
  mutable : start.entry.allocation.mutability = .Mut
  bufferExtras : start.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == start.id) = some (start.id,⟨none,#[]⟩)
  bounded : start.count ≤ (PreparedContracts.actualConfig start.options () (start.remaining+1) start.span).projection.maxSizeOfVal.bytes
  zero : start.caller.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
  continuation : start.caller.returnContinuation = .stop true
  varargs : start.caller.vaList = #[]
  context : Context
  validationContext : Context
  accessEq : (PreparedContracts.actualConfig start.options () start.remaining start.span).access = validationContext.access
  validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8
  sameRuntime : validationContext.access.runtime.base = context.access.runtime.base
  width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  runtimeWidth : context.access.runtime.base.pointerWidth = .w64
  runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8
  outerAccessEq : (PreparedContracts.actualConfig start.options () (start.remaining+1) start.span).access = context.access
  slotId : AllocId
  separate : slotId ≠ start.id
  slot : LocalAllocation Provenance BorrowTree MiriMemoryKind
  slotPresent : start.machine.memory.live.find? (fun row => row.1 == slotId) = some (slotId,slot)
  slotRoot : BorTag
  slotChild : BorTag
  slotTree : slot.allocation.extra = slotTree slotRoot slotChild 1 true
  slotRootNotHelper : start.tracker.global.nextPointerTag ≠ slotRoot
  slotRootFree : start.tracker.global.protectedTags.contains slotRoot = false
  slotChildHeld : start.tracker.global.protectedTags.contains slotChild = true
  slotDistinct : slotRoot ≠ slotChild
  slotChildNotHelper : slotChild ≠ start.tracker.global.nextPointerTag
  frameTracked : start.caller.extra.borrowTracker = some
    ((({} : FrameState).addProtector start.id targetTag).addProtector slotId slotChild)
  slotSize : slot.allocation.byteSize = Size.ofBytes 1
  slotStorage : slot.allocation.len = 1
  slotMask : slot.allocation.initializationMask = InitMask.new (Size.ofBytes 1) false
  slotProvenance : slot.allocation.provenanceMap = ProvenanceMap.new
  slotMutable : slot.allocation.mutability = .Mut
  place : MPlaceTy Provenance
  layout : place.layout = RootCompilerFacts.boolLayout
  slotBase : UInt64
  slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase)
  aligned : place.mplace.misaligned = none
  fits : slotBase.toNat + 1 < 2^64
  cached : start.machine.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩
  extras : start.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩)
  destination : start.caller.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩


/-- Compose the real source call entry with mutable helper execution, copy,
protector releases and physical true return. All intermediate contracts are
constructed from the pre-call data. -/
theorem complete_full (input : Input) :
    let s := input.start
    let destination := (LocalPlaces.localRuntimePlace 0 s.caller 15 CopyCompilerFacts.destPointerLayout).stackView
    ∃ ready : GeneralBorrowForestAsMutPhysicalReturn.Input,
      ready.start.caller = s.caller ∧
      PreparedContracts.actualConfig ready.start.options () (ready.start.remaining+1) ready.start.span =
        PreparedContracts.actualConfig s.options () (s.remaining+1) s.span ∧
      ready.start.limits = s.limits ∧
      Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span) s.limits) ()
        HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
        #[.Copy ⟨.immediate (GeneralBorrowForestAsMutInvocationCore.parent s),ActualReferenceMetadata.reference⟩]
        false destination (.goto (some 7) .Continue) (Storage.withCurrent #[] s.caller s.machine) =
        .ok () (Storage.withCurrent #[s.caller] (GeneralBorrowForestAsMutBodyToCopy.helper ready.start) ready.start.machine) ∧
      GeneralBorrowForestAsMutPhysicalReturn.Result ready := by
  let s := input.start
  have lenNonzero : s.len ≠ 0 := by
    intro zero
    have bad := s.positive
    rw [zero] at bad
    exact (show ¬ ((0 : UInt64) < 0) from by decide) bad
  have bounds : s.offset.toNat+s.len.toNat ≤ s.entry.allocation.extra.locations.size.bytes.toNat := by
    rw [s.capacity]
    exact s.bounds
  have addition : (s.offset+s.len).toNat = s.offset.toNat+s.len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt_size s.entry.allocation.extra.locations.size.bytes)
  have positive : s.offset.toNat < (s.offset+s.len).toNat := by
    rw [addition]
    have lp : 0 < s.len.toNat := s.positive
    omega
  obtain ⟨release,anchor,lower,upper,primary,extraRoots,capacity,targetStrong,oldLookup,oldNode⟩ := GeneralBorrowForestAsMutEntryTree.prepare
    s.entry.allocation.extra s.tracker s.parentTag s.offset s.len s.data positive lenNonzero bounds s.clean input.target input.targetWithin
  obtain ⟨targetNode,targetPresent,targetTag,targetExposure⟩ := oldNode input.target input.targetNode input.targetPresent
  have paths := GeneralBorrowForestAsMutEntryPaths.prepare s.entry.allocation.extra s.tracker s.parentTag s.offset s.len s.data
    lenNonzero bounds input.target input.targetNode input.targetPresent input.subset input.escaping
  let body := GeneralBorrowForestAsMutInvocationCore.body_input s release
  have push := GeneralBorrowForestAsMutEntryState.push_fields s.options.userRelevantCrates s.caller s.machine
    (LocalPlaces.localRuntimePlace 0 s.caller 15 CopyCompilerFacts.destPointerLayout).stackView s.thread s.active
  have memory : (GeneralBorrowForestAsMutInvocationCore.pushed s).memory = s.machine.memory := push.1
  have user : (GeneralBorrowForestAsMutInvocationCore.pushed s).user.payload.payload.user = s.machine.user.payload.payload.user := push.2.2.2.2.2.1
  have addresses : (GeneralBorrowForestAsMutInvocationCore.pushed s).user.addresses = s.machine.user.addresses := push.2.2.2.2.2.2.1
  have bodyAnchor : body.release.anchor = GeneralBorrowFreshMutableStages.slot_index s.data.slot := anchor
  let ready : GeneralBorrowForestAsMutPhysicalReturn.Input := by
    refine {
      start := body, statementFuel := input.statementFuel, releaseLower := lower, releaseUpper := upper
      capacity := capacity.trans s.capacity
      target := input.target, targetNode := targetNode, targetPresent := targetPresent
      targetNotExposed := targetExposure.trans input.targetNotExposed, targetTag := input.targetTag
      targetTagPresent := (oldLookup input.targetTag input.targetNotHelper).trans input.targetTagPresent
      covered := GeneralBorrowForestAsMutEntryTree.covered s.entry.allocation.extra s.tracker s.parentTag s.offset s.len s.data lenNonzero bounds
      targetContext := {
        anchorNode := targetNode,primaryNode := release.context.primaryNode,depth := release.context.depth,children := release.context.children
        anchorPresent := targetPresent,primaryPresent := release.context.primaryPresent,roots := release.context.roots
        different := release.context.different,unexposed := release.context.unexposed }
      targetRootPath := ?_
      targetWithin := targetStrong, subset := ?_, escaping := ?_
      storage := input.storage,
      maskValid := input.maskValid,
      maskLength := input.maskLength,
      initialized := input.initialized,
      provenance := input.provenance,
      storageFits := input.storageFits,
      mutable := input.mutable,
      bounded := input.bounded,
      zero := input.zero,
      continuation := input.continuation,
      varargs := input.varargs,
      context := input.context,
      validationContext := input.validationContext,
      accessEq := input.accessEq,
      validationWidth := input.validationWidth,
      validationRuntimeSize := input.validationRuntimeSize,
      sameRuntime := input.sameRuntime,
      width := input.width,
      runtimeWidth := input.runtimeWidth,
      runtimeSize := input.runtimeSize,
      outerAccessEq := input.outerAccessEq,
      slotId := input.slotId,
      separate := input.separate,
      slot := input.slot,
      slotRoot := input.slotRoot,
      slotChild := input.slotChild,
      slotTree := input.slotTree,
      slotDistinct := input.slotDistinct,
      slotChildNotHelper := input.slotChildNotHelper,
      frameTracked := input.frameTracked,
      slotSize := input.slotSize,
      slotStorage := input.slotStorage,
      slotMask := input.slotMask,
      slotProvenance := input.slotProvenance,
      slotMutable := input.slotMutable,
      place := input.place,
      layout := input.layout,
      slotBase := input.slotBase,
      slotPointer := input.slotPointer,
      aligned := input.aligned,
      fits := input.fits,
      destination := input.destination,
      bufferExtras := ?_, slotPresent := ?_, slotRootFree := ?_, slotChildHeld := ?_, cached := ?_, extras := ?_ }
    · intro location
      change ((source_normal_projection (GeneralBorrowForestArgumentCopy.finalTree s.entry.allocation.extra s.tracker s.parentTag s.offset s.len)
        location (GeneralBorrowForestAsMutEntryState.tracker s.tracker s.fresh).global.protectedTags).topology.ancestorPath input.target.toNat).getLast! = release.primary.toNat
      rw [primary]
      have path := GeneralBorrowForestAsMutEntryPaths.target_path s.entry.allocation.extra s.tracker s.parentTag s.offset s.len s.data
        lenNonzero bounds input.target input.targetNode input.targetPresent input.subset input.escaping location
      rw [GeneralBorrowFreshMutablePathData.topology_any _ location location _ s.tracker.global.protectedTags,path]
      exact input.targetRootPath location
    · intro location position member
      rw [bodyAnchor]
      exact paths.1 location position member
    · intro location index node present localChild foreignTarget
      rw [bodyAnchor] at localChild
      rcases paths.2 location index node present localChild foreignTarget with unheld | fresh
      · exact Or.inl unheld
      · apply Or.inr
        refine ⟨s.id,?_⟩
        change (s.id,node.tag) ∈ ((({} : FrameState).addProtector s.id s.tracker.global.nextPointerTag).protectedTags.toList)
        simpa only [FrameState.addProtector,Array.toList_push,Array.toList_empty,List.nil_append,List.mem_cons,List.not_mem_nil,
          or_false,Prod.mk.injEq] using (show s.id = s.id ∧ node.tag = s.tracker.global.nextPointerTag from ⟨rfl,fresh⟩)
    · change (GeneralBorrowForestAsMutInvocationCore.pushed s).user.payload.payload.user.runtime.extras.allocations.find? _ = _
      rw [user]
      exact input.bufferExtras
    · have present : (GeneralBorrowForestAsMutInvocationCore.pushed s).memory.live.find? (fun row => row.1 == input.slotId) = some (input.slotId,input.slot) := by
        rw [memory]
        exact input.slotPresent
      exact StackPopRelease.lookup_commit_other (GeneralBorrowForestAsMutInvocationCore.pushed s).memory s.id input.slotId s.entry input.slot _ input.separate present
    · change (s.tracker.global.protectedTags.insert s.tracker.global.nextPointerTag .StrongProtector).contains input.slotRoot = false
      rw [ProtectorInsertion.contains_other _ _ _ _ (Ne.symm input.slotRootNotHelper)]
      exact input.slotRootFree
    · change (s.tracker.global.protectedTags.insert s.tracker.global.nextPointerTag .StrongProtector).contains input.slotChild = true
      rw [ProtectorInsertion.contains_other _ _ _ _ input.slotChildNotHelper]
      exact input.slotChildHeld
    · change (GeneralBorrowForestAsMutInvocationCore.pushed s).user.addresses.baseAddr.find? _ = _
      rw [addresses]
      exact input.cached
    · change (GeneralBorrowForestAsMutInvocationCore.pushed s).user.payload.payload.user.runtime.extras.allocations.find? _ = _
      rw [user]
      exact input.extras
  exact ⟨ready,rfl,rfl,rfl,GeneralBorrowForestAsMutInvocationCore.actual_entry s release,GeneralBorrowForestAsMutPhysicalReturn.complete ready⟩


/-- Compose the real source call entry with mutable helper execution, copy,
protector releases and physical true return. All intermediate contracts are
constructed from the pre-call data. -/
theorem complete (input : Input) :
    let s := input.start
    let destination := (LocalPlaces.localRuntimePlace 0 s.caller 15 CopyCompilerFacts.destPointerLayout).stackView
    ∃ ready : GeneralBorrowForestAsMutPhysicalReturn.Input,
      ready.start.caller = s.caller ∧
      Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig s.options () (s.remaining+1) s.span) s.limits) ()
        HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
        #[.Copy ⟨.immediate (GeneralBorrowForestAsMutInvocationCore.parent s),ActualReferenceMetadata.reference⟩]
        false destination (.goto (some 7) .Continue) (Storage.withCurrent #[] s.caller s.machine) =
        .ok () (Storage.withCurrent #[s.caller] (GeneralBorrowForestAsMutBodyToCopy.helper ready.start) ready.start.machine) ∧
      GeneralBorrowForestAsMutPhysicalReturn.Result ready := by
  obtain ⟨ready,caller,_,_,entry,result⟩ := complete_full input
  exact ⟨ready,caller,entry,result⟩

end DuplicatePrefix.GeneralBorrowForestAsMutInvocation
