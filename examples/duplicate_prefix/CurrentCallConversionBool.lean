import duplicate_prefix.CurrentCallConversionSourceCopy
import duplicate_prefix.CurrentCallLazyBoolTyped
import duplicate_prefix.CurrentCallLiveBoolTransport

/-! Actual latent Bool protection through the finite CURRENT converter. The
source-neutral producer keeps the real registered phase and saved Bool tag,
without imposing a data-only image or an initially LIVE Bool allocation. -/
namespace DuplicatePrefix.CurrentCallConversionBool
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata TypedBorrowSteps
open GeneralBorrowFullSharedSeed CurrentCallLazyBoolEnsure CurrentCallFamilySatisfaction
open ReferenceBorrowDriver CurrentCallOrdinaryInput CurrentCallConversionSourceCopy
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem reborrow (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (machine : Before) (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (root tag : BorTag) (source : Allocation CtfeProvenance Unit)
    (base offset : UInt64) (place : MPlaceTy Provenance)
    (pointerEq : place.mplace.ptr = Pointer.new (some (.concrete id root)) (Size.ofBytes (base + offset)))
    (layout : place.layout = RootCompilerFacts.boolLayout) (current : CurrentPayload machine id source)
    (absent : machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : machine.memory.hasFunctionPointer id = false) (noVaList : machine.memory.hasVaListId id = false)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (bounds : offset.toNat + 1 ≤ source.byteSize.bytes.toNat)
    (rootBelow : root.value.toNat < tag.value.toNat)
    (protectorBelow : ∀ row ∈ tracker.global.protectedTags.entries, row.1.value.toNat < tag.value.toNat)
    (tagRoom : tag.value < 18446744073709551615)
    (converted : Allocation Provenance Unit) (attributes : GlobalAllocationAttributes.Attributes source converted)
    (after : Before) (afterTracker : MachineHooks.BorrowState)
    (conversion : Allocation.adjustFromTcx source PreparedReflection.actual.compiler.runtime.target.base
      (fun _ _ state => .ok (AllocationCopy.snapshot source) state)
      (CurrentCallConversionActualEnsure.hooks options).rootPointer
      (registeredState frames frame borrowFrame machine tracker id tag).machine = .ok converted after)
    (afterEnabled : after.borrowTracker = some afterTracker)
    (afterRoot : afterTracker.global.rootTag? id = some root) (afterRace : after.dataRace = none)
    (afterExtras : (after.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (flags : afterTracker.global.protectedTags = (registeredGlobal tracker tag).protectedTags) :
    let h := (config options remaining span).retag
    TypedRetag.reborrow h options.limits.retag place (Size.ofBytes 1) MachineHooks.protectionPolicy tag
      (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
          (childMachine options after id root tag converted (registeredGlobal tracker tag).protectedTags offset 1)) := by
  let h := (config options remaining span).retag
  let start := Storage.withCurrent frames frame machine
  let registered := registeredState frames frame borrowFrame machine tracker id tag
  have info : machine.memory.getAllocInfo id = .ok ⟨source.byteSize, source.align, .liveData, source.mutability⟩ := by
    cases current with
    | memory descriptor => exact GlobalDataOnlyMaterialize.alloc_info machine id source absent noFunction noVaList descriptor
    | internalStatic definition descriptor row =>
      exact StaticGlobalAllocInfo.alloc_info machine id source definition absent noFunction noVaList descriptor
  have check : h.checkPtrAccess place.mplace.ptr (Size.ofBytes 1) start = .ok () start := by
    rw [ctx.source.check, pointerEq]
    exact (positive_global_rule ".PositiveGlobalTypedReborrow.check_known") ctx.pointers (config options remaining span).access
      start id root base offset 1 _ ctx.resolve ctx.arithmetic cached info rfl (by decide) (by decide) bounds
  have resolve : h.resolveAllocation place.mplace.ptr start = .ok (some ⟨id, Size.ofBytes offset, .concrete root⟩) start := by
    rw [ctx.source.resolve, pointerEq]
    exact RetagPointerChecks.resolve_allocation_cached ctx.pointers start id root base offset ctx.arithmetic cached
  have frozen : h.typeIsFreeze place.layout.ty = pure true := by
    rw [layout]
    exact ActualRetagContext.bool_freeze options remaining span ctx
  have inside := TypedRetagPolicyFields.inside_for_policy h options.limits.retag place (Size.ofBytes 1)
    MachineHooks.protectionPolicy ChildBorrow.fnEntryLocation rfl ctx.source.precise frozen
  have registeredCurrent : CurrentPayload registered.machine id source := by
    cases current with
    | memory descriptor => exact .memory descriptor
    | internalStatic definition descriptor row => exact .internalStatic definition descriptor row
  have ensure := CurrentCallConversionActualEnsure.ensure options remaining span registered after afterTracker id root source converted
    registeredCurrent absent conversion afterEnabled afterRoot afterRace afterExtras
  have present : (rootMachine options after id root converted).memory.live.find? (fun row => row.1 == id) =
      some (id, rootEntry root converted) := MemoryCopyBridge.live_lookup_replaced _ _ _
  let parent := (BorrowTree.new root converted.byteSize).performBorrowAccessRange (.concrete root)
    (Size.ofBytes offset) (Size.ofBytes 1) .Read afterTracker.global.protectedTags .VisitChildrenOfAccessed
  let child := parent.tree.newChild (Size.ofBytes offset) (.concrete root) tag
    (DedupRangeMap.new (Size.ofBytes 1) ChildBorrow.fnEntryLocation) (.ReservedFrz false) true
  have stages := (positive_global_rule ".PositiveGlobalTypedReborrow.read_child") root tag
    source.byteSize.bytes offset 1 tracker.global.protectedTags (by decide) bounds rootBelow protectorBelow tagRoom
  have readDone : parent.status = .Completed := by
    dsimp only [parent]
    rw [attributes.size, flags]
    exact stages.1
  have childDone : parent.tree.newChild (Size.ofBytes offset) (.concrete root) tag
      (DedupRangeMap.new (Size.ofBytes 1) ChildBorrow.fnEntryLocation)
      MachineHooks.protectionPolicy.outsidePermission MachineHooks.protectionPolicy.protector.isSome = ⟨child.tree, .ok ()⟩ := by
    dsimp only [parent, child]
    rw [attributes.size, flags]
    exact GeneralBorrowFreshReborrowStages.child_complete _ stages.2
  have initialInfo : machine.memory.getAllocInfo id = .ok
      ⟨(rootEntry root converted).allocation.byteSize, (rootEntry root converted).allocation.align,
        .liveData, (rootEntry root converted).allocation.mutability⟩ := by
    change machine.memory.getAllocInfo id = .ok ⟨converted.byteSize, converted.align, .liveData, converted.mutability⟩
    rw [attributes.size, attributes.align, attributes.mutability]
    exact info
  have actual := CurrentCallTypedAfterEnsure.protected_reborrow h options.limits.retag place frames frame borrowFrame
    machine tracker enabled frameBorrow id (rootEntry root converted) offset 1 (.concrete root) tag
    ChildBorrow.fnEntryLocation MachineHooks.protectionPolicy rfl rfl
    (by decide)
    check resolve (by rw [ctx.source.log]) inside initialInfo (rootMachine options after id root converted) afterTracker
    ensure afterEnabled present afterRace parent.tree child.tree rfl readDone childDone
  simpa only [childMachine, PositiveGlobalTypedReborrow.finalTree, parent, child, flags] using actual




/-- Actual Bool tag allocation and registered lazy conversion from the original state. -/
theorem retag (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (machine : Before) (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (base offset : UInt64) (place : MPlaceTy Provenance)
    (pointerEq : place.mplace.ptr = Pointer.new (some (.concrete id root)) (Size.ofBytes (base + offset)))
    (layout : place.layout = RootCompilerFacts.boolLayout) (current : CurrentPayload machine id source)
    (absent : machine.memory.live.find? (fun row => row.1 == id) = none)
    (noFunction : machine.memory.hasFunctionPointer id = false) (noVaList : machine.memory.hasVaListId id = false)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (bounds : offset.toNat + 1 ≤ source.byteSize.bytes.toNat)
    (rootBelow : root.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (protectorBelow : ∀ row ∈ tracker.global.protectedTags.entries, row.1.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (converted : Allocation Provenance Unit) (attributes : GlobalAllocationAttributes.Attributes source converted)
    (after : Before) (afterTracker : MachineHooks.BorrowState)
    (conversion : Allocation.adjustFromTcx source PreparedReflection.actual.compiler.runtime.target.base
      (fun _ _ state => .ok (AllocationCopy.snapshot source) state)
      (CurrentCallConversionActualEnsure.hooks options).rootPointer
      (registeredState frames frame borrowFrame (allocatedMachine machine tracker fresh)
        (allocatedTracker tracker fresh) id tracker.global.nextPointerTag).machine = .ok converted after)
    (afterEnabled : after.borrowTracker = some afterTracker)
    (afterRoot : afterTracker.global.rootTag? id = some root) (afterRace : after.dataRace = none)
    (afterExtras : (after.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == id)) = false)
    (flags : afterTracker.global.protectedTags = (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags) :
    TypedRetag.retagPlace (config options remaining span).retag options.limits.retag place MachineHooks.protectionPolicy
      (Storage.withCurrent frames frame machine) =
      .ok (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag)
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
          (childMachine options after id root tracker.global.nextPointerTag converted afterTracker.global.protectedTags offset 1)) := by
  have allocatedCurrent : CurrentPayload (allocatedMachine machine tracker fresh) id source := by
    cases current with
    | memory descriptor => exact .memory descriptor
    | internalStatic definition descriptor row => exact .internalStatic definition descriptor row
  have borrowed := reborrow options remaining span ctx frames frame borrowFrame frameBorrow
    (allocatedMachine machine tracker fresh) (allocatedTracker tracker fresh) rfl id root tracker.global.nextPointerTag
    source base offset place pointerEq layout allocatedCurrent absent noFunction noVaList cached bounds rootBelow protectorBelow
    fresh converted attributes after afterTracker conversion afterEnabled afterRoot afterRace afterExtras flags
  apply retag_place_of_reborrow (config options remaining span).retag options.limits.retag place MachineHooks.protectionPolicy
    (Size.ofBytes 1) Align.ONE (Storage.withCurrent frames frame machine) _ tracker enabled fresh id (.concrete id root)
    (by rw [pointerEq]; rfl) (ActualRetagContext.bool_size options remaining span ctx place layout)
  simpa only [flags, TypedRetagEmpty.afterTag, Storage.withCurrent, allocatedMachine, allocatedTracker] using borrowed


theorem root_view (machine : Before) (tracker : MachineHooks.BorrowState)
    (family : CurrentCallSpatialCover.Family) (root : BorTag)
    (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit)
    (attributes : GlobalAllocationAttributes.Attributes source converted)
    (convertedWF : ProvenanceCopy.WellFormed converted.provenanceMap converted.len)
    (base offset : UInt64) (place : MPlaceTy Provenance)
    (value : family.value = Pointer.new (.concrete family.allocation root) (Size.ofBytes (base + offset)))
    (physicalPointer : place.mplace.ptr = family.value.withOptionalProvenance)
    (layout : place.layout = RootCompilerFacts.boolLayout) (aligned : place.mplace.misaligned = none)
    (physical : Physical source offset 1 false)
    (live : machine.memory.live.find? (fun row => row.1 == family.allocation) =
      some (family.allocation, ⟨.machine .global, converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)⟩))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == family.allocation) = some ⟨family.allocation, base⟩)
    (rootCached : tracker.global.rootTag? family.allocation = some root)
    (addressRoom : base.toNat + source.len < 2^64) (nonnull : base + offset ≠ 0)
    (rootBelow : root.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (protectors : ∀ row ∈ tracker.global.protectedTags.entries,
      row.1.value.toNat < tracker.global.nextPointerTag.value.toNat) :
    let allocation := converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)
    AllocationCapability machine tracker family.allocation allocation ∧
    DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global ∧
    CandidateCallBindings.WindowBinding machine family.value family.allocation offset.toNat 1 ∧
    CurrentCallFamilySatisfaction.Satisfies tracker family allocation (Window family.allocation offset.toNat 1) ∧
    ∃ physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place,
      physical.id = family.allocation ∧ physical.pointer = family.value ∧ physical.entry.allocation = allocation ∧ physical.offset = offset ∧
    ∃ B : UniformWindow machine tracker
      (CurrentCallLazyBoolEnsure.identities family (CurrentCallLazyBoolEnsure.completion root source.byteSize)) 0
      physical.id physical.offset.toNat 1 .ret,
      B.pointer = family.at allocationRoot ∧ B.allocation = allocation := by
  have storage := physical.1.1
  have mutable := physical.2.1
  have bounds : offset.toNat + 1 ≤ source.byteSize.bytes.toNat := by
    simpa only [UInt64.toNat_one] using physical.2.2.1
  have maskValid := physical.1.2.1
  have maskLength := physical.1.2.2.1
  let allocation:=converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)
  let after := machine
  have nonzero : source.byteSize.bytes≠0:=by
    intro zero
    have bounds:=bounds
    rw [zero] at bounds
    simp only [UInt64.toNat_zero] at bounds
    omega
  have shape:=tree_eq source.byteSize.bytes nonzero root
  change BorrowTree.new root (Size.ofBytes source.byteSize.bytes)=_ at shape
  have length : allocation.len=allocation.byteSize.bytes.toNat:=by
    change converted.len=converted.byteSize.bytes.toNat
    rw [attributes.storage,attributes.size]
    exact storage
  have treeSize : allocation.extra.locations.size=allocation.byteSize:=by
    change (BorrowTree.new root source.byteSize).locations.size=converted.byteSize
    rw [attributes.size]
    exact (by rw [show source.byteSize=Size.ofBytes source.byteSize.bytes from rfl,shape];rfl)
  have cap : AllocationCapability after tracker family.allocation allocation:=by
    refine ⟨?_,length,treeSize,rfl,_,BorrowTree.new_root_node _ _,rfl,rfl,rootCached⟩
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(family.allocation,⟨.machine .global,allocation⟩),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global:=
    S03MaterializableRootRuntime.initial root source.byteSize.bytes tracker.global rootBelow protectors
  have parents : ParentInterpretation allocation.extra (CurrentCallLazyBoolEnsure.completion root source.byteSize):=by
    exact ((positive_global_rule ".CurrentCallLazyBoolEnsure.rootChain") root source.byteSize).parents runtime.formed.toGraphState
      (GeneralBorrowParentTagRootFrames.new_root root source.byteSize) (by change ([allocationRoot] : List UniIndex).Nodup;simp)
      _ (BorrowTree.new_root_node root source.byteSize) rfl
  have pointerBind : PointerBinds allocation (family.at allocationRoot):=by
    refine ⟨_,BorrowTree.new_root_node _ _,runtime.formed.allocator.nodeTags _ _ (BorrowTree.new_root_node _ _),?_⟩
    change (match family.value.provenance with | .concrete id tag=>id=family.allocation ∧tag=root | .wildcard=>false=true)
    rw [value]
    exact ⟨rfl,rfl⟩
  have offsetBound : offset.toNat≤source.len:=by have bounds:=bounds;rw [storage];omega
  have sumFits : base.toNat+offset.toNat<2^64:=by have room:=addressRoom;omega
  have binding : CandidateCallBindings.WindowBinding after family.value family.allocation offset.toNat 1:=by
    refine ⟨⟨.machine .global,allocation⟩,base,live,cached,length,?_,?_,?_,?_,?_⟩
    · change base.toNat+converted.len<2^64
      rw [attributes.storage]
      exact addressRoom
    · change offset.toNat+1≤converted.len
      rw [attributes.storage,storage]
      exact bounds
    · rw [value]
      change (base+offset).toNat=base.toNat+offset.toNat
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt sumFits]
    · rw [value]
      exact nonnull
    · rw [value]
      rfl
  let physical : CandidateCurrentBoolUninitWrite.PhysicalWindow after place:={
    pointer:=family.value,physicalPointer:=physicalPointer,layout:=layout,aligned:=aligned,
    id:=family.allocation,entry:=⟨.machine .global,allocation⟩,base:=base,offset:=offset,capacity:=source.byteSize.bytes,
    live:=live,cachedBase:=cached,pointerAddress:=by rw [value];rfl,
    bounds:=bounds,size:=attributes.size,bytes:=by change converted.len=source.byteSize.bytes.toNat;rw [attributes.storage,storage],
    mutable:=attributes.mutability.trans mutable,
    maskValid:=by change InitMaskCopy.WellFormed converted.initializationMask;rw [attributes.mask];exact maskValid,
    maskLength:=by change converted.initializationMask.len=Size.ofBytes source.byteSize.bytes;rw [attributes.mask];exact maskLength,
    provenanceMap:=convertedWF}
  let B : UniformWindow after tracker (CurrentCallLazyBoolEnsure.identities family (CurrentCallLazyBoolEnsure.completion root source.byteSize)) 0 family.allocation offset.toNat 1 .ret:={
    loan:=⟨0,none,0⟩,pointer:=family.at allocationRoot,allocation:=allocation,precise:=⟨completion root source.byteSize,#[]⟩,
    loanAt:=rfl,pointerAt:=rfl,pointerId:=rfl,present:=cap.live,preciseAt:=by simp [identities],
    binding:=pointerBind,issued:=.allocated cap,parents:=parents,
    window:=by
      intro byte hit
      refine ⟨?_,(positive_global_rule ".CurrentCallLazyBoolEnsure.seed_embeds") allocation source.byteSize.bytes root nonzero rfl tracker.global.protectedTags _ byte.2⟩
      change byte.2<converted.len
      rw [attributes.storage,storage]
      have bound:=bounds
      have upper:=hit.2.2
      omega}
  have owned : Satisfies tracker family allocation (Window family.allocation offset.toNat 1):=by
    intro byte hit
    obtain ⟨chain,_,support⟩:=CurrentCallSupportChainExtraction.extract_support B.parents B.issued (B.window byte hit).2
    exact ⟨hit.1,allocationRoot,chain,pointerBind,support⟩
  exact ⟨cap,runtime,binding,owned,physical,rfl,rfl,rfl,rfl,B,rfl,rfl⟩


private theorem runtime_mono {tree : BorrowTree} {old next : GlobalState}
    (facts : DuplicatePrefixBorrowContract.RuntimeFacts tree old)
    (flags : next.protectedTags = old.protectedTags)
    (counter : old.nextPointerTag.value.toNat ≤ next.nextPointerTag.value.toNat) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree next := by
  refine ⟨?_, ?_, facts.possible, ?_, ?_⟩
  · simpa only [flags] using facts.formed
  · simpa only [flags] using facts.coherent
  · intro row member
    have := facts.below.mapping row member
    omega
  · intro row member
    rw [flags] at member
    have := facts.below.protectors row member
    omega

private theorem return_view {before tracker data owner place}
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (selected : UniformWindow before tracker data owner physical.id physical.offset.toNat 1 .ret)
    (samePointer : physical.pointer = selected.pointer.value)
    (sameAllocation : physical.entry.allocation = selected.allocation)
    (selectedRun : DuplicatePrefixBorrowContract.RuntimeFacts selected.allocation.extra tracker.global)
    (selectedBinding : CandidateCallBindings.WindowBinding before physical.pointer physical.id physical.offset.toNat 1)
    (distinct : selected.allocation.extra.roots.toList.Nodup)
    (borrowFrame : FrameState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (short : selected.allocation.extra.nodes.size + 1 < 65536)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (actual : CandidateCurrentFnEntryRaw.operation selected.allocation.extra tracker.global borrowFrame physical.id
      selected.pointer.value.provenance physical.offset 1 = .ok output)
    (witness : CurrentCallResourceFnEntry.BorrowWitness selected output child physical.offset 1)
    (tag : output.tag = tracker.global.nextPointerTag)
    (constructor : Before)
    (constructorPresent : Present (ActualWorld constructor) physical.id (selected.allocation.setExtra output.child.tree))
    (rootTag : output.global.rootTag? physical.id = tracker.global.rootTag? physical.id)
    (post : Before) (updated : Allocation Provenance BorrowTree)
    (live : post.memory.live.find? (fun row => row.1 == physical.id) =
      some (physical.id, {physical.entry with allocation := updated}))
    (addresses : post.user.addresses = before.user.addresses)
    (ready : CurrentCallBoolProtection.WindowReady post physical.id physical.offset.toNat 1)
    (sizeEq : updated.byteSize = physical.entry.allocation.byteSize)
    (lengthEq : updated.len = physical.entry.allocation.len) (mutable : updated.mutability = .Mut)
    (extraSelected : updated.extra = (output.child.tree.performBorrowAccessRange (.concrete output.tag)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed).tree)
    (write : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
      ((physical.entry.allocation.setExtra output.child.tree).setExtra
        (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
          .Write output.global.protectedTags .VisitChildrenOfAccessed).tree) = .ok () updated)
    (next : MachineHooks.BorrowState) (flags : next.global.protectedTags = output.global.protectedTags)
    (counter : output.global.nextPointerTag.value.toNat ≤ next.global.nextPointerTag.value.toNat)
    (rootHit : ∀ tag, output.global.rootTag? physical.id = some tag → next.global.rootTag? physical.id = some tag) :
    ∃ R : CurrentCallPostEntryCheckpoint.Return post next place,
      R.id = physical.id ∧ R.offset = physical.offset.toNat ∧ R.original = selected.pointer ∧
      R.window.allocation = updated ∧ R.node.tag = output.tag ∧
      R.window.allocation.extra.nodes.size ≤ selected.allocation.extra.nodes.size + 1 := by
  have finalPresent : Present (ActualWorld post) physical.id updated := by
    simp only [Present, ActualWorld, Array.toList_map]
    exact List.mem_map.mpr ⟨_, Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live), rfl⟩
  have sizeSelected : updated.byteSize = selected.allocation.byteSize := sizeEq.trans (congrArg Allocation.byteSize sameAllocation)
  have lengthSelected : updated.len = selected.allocation.len := lengthEq.trans (congrArg Allocation.len sameAllocation)
  obtain ⟨nextData, nextOwner, Q, pointerQ, allocationQ, completionQ, currentRuntime, _, leaf, hidden, nodeAtFinal,
      active, parentIssued, parentBinding⟩ := CurrentCallSelectedBoolWindow.window selected selectedRun borrowFrame fresh
    distinct short physical.offset rfl output child actual witness tag constructor constructorPresent rootTag
    post updated finalPresent lengthSelected sizeSelected extraSelected
  have currentIssued := CurrentCallLiveBoolTransport.spatial Q.issued post next Q.present rootHit
  let Rwindow : UniformWindow post next nextData nextOwner physical.id physical.offset.toNat 1 .ret := {
    loan := Q.loan, pointer := Q.pointer, allocation := Q.allocation, precise := Q.precise,
    loanAt := Q.loanAt, pointerAt := Q.pointerAt, pointerId := Q.pointerId, present := Q.present,
    preciseAt := Q.preciseAt, binding := Q.binding, issued := currentIssued, parents := Q.parents,
    window := by intro byte inside; simpa only [flags] using Q.window byte inside }
  let mutationInput := (physical.entry.allocation.setExtra output.child.tree).setExtra
    (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write output.global.protectedTags .VisitChildrenOfAccessed).tree
  obtain ⟨other, otherWrite, _, _, _, _, _, maskValid, maskLen, clear⟩ := S02SameDestinationUninitInitializedMutation.uninit
    mutationInput physical.capacity physical.offset physical.bytes physical.size physical.mutable
    physical.maskValid physical.maskLength physical.provenanceMap physical.bounds
  have equal : other = updated := by injection (otherWrite.symm.trans write)
  subst other
  have endpoint := (DuplicatePrefix.source_end (Size.ofBytes physical.offset) 1 (by
    have bound := physical.bounds
    have room := physical.capacity.toNat_lt
    simpa [Size.ofBytes] using (show physical.offset.toNat + 1 < 2^64 by omega)))
  have pointerBounds := S03UninitProvenance.clear_pointer_bounds mutationInput.provenanceMap updated.provenanceMap
    (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes (physical.offset + 1))
    (AllocationCopy.snapshot mutationInput) mutationInput.len endpoint
    (ProvenanceCopy.WellFormed.pointerBounds physical.provenanceMap) clear
  let P : CurrentCallBoolScalarWrite.Window post place := {
    pointer := physical.pointer, physicalPointer := physical.physicalPointer, layout := physical.layout, aligned := physical.aligned,
    id := physical.id, entry := {physical.entry with allocation := updated}, base := physical.base, offset := physical.offset,
    capacity := physical.capacity, live := live, cachedBase := by rw [addresses]; exact physical.cachedBase,
    pointerAddress := physical.pointerAddress, bounds := physical.bounds, size := sizeEq.trans physical.size,
    bytes := lengthEq.trans physical.bytes, mutable := mutable, maskValid := maskValid,
    maskLength := maskLen.trans physical.maskLength, pointerBounds := by rw [lengthEq]; exact pointerBounds }
  have windowBounds : physical.offset.toNat + 1 ≤ selected.allocation.extra.locations.size.bytes.toNat := by
    rw [selected.issued.capability.treeExtent, ← selected.issued.capability.extent]
    have hit := (selected.window (physical.id, physical.offset.toNat) ⟨rfl, by omega, by omega⟩).1
    omega
  obtain ⟨_, _, _, _, nodes, roots, _, _⟩ := CurrentCallSelectedBoolCurrent.operation_runtime selected selectedRun borrowFrame fresh
    distinct short physical.offset rfl output child actual witness tag constructor constructorPresent rootTag .VisitChildrenOfAccessed
  have finalDistinct : updated.extra.roots.toList.Nodup := by
    have rootAfter := (positive_global_rule ".CurrentCallSelectedBoolProtection.roots") selected selectedRun borrowFrame fresh
      rfl distinct (by omega) (by omega) physical.offset 1 rfl rfl (by decide) windowBounds output actual
    rw [extraSelected, roots]
    exact rootAfter
  have finalGrowth : updated.extra.nodes.size ≤ selected.allocation.extra.nodes.size + 1 := by
    have bound := (positive_global_rule ".CurrentCallSelectedBoolProtection.growth") selected selectedRun borrowFrame fresh rfl distinct
      (by omega) (by omega) physical.offset 1 rfl rfl (by decide) windowBounds output actual
    rw [extraSelected, nodes]
    exact bound
  have finalShort : updated.extra.nodes.size < 65536 := by omega
  have originalIssued : SpatialDelegation post next physical.id Q.allocation Q.precise.completion selected.pointer.grant := by
    rw [allocationQ]
    exact CurrentCallLiveBoolTransport.spatial parentIssued post next finalPresent rootHit
  have finalBinding : CandidateCallBindings.WindowBinding post P.pointer physical.id physical.offset.toNat 1 := by
    obtain ⟨old, address, oldLive, cachedAddress, storage, addressRoom, bounds, pointerAddress, nonnull, provenance⟩ := selectedBinding
    have oldEq : old = physical.entry := (Prod.mk.inj (Option.some.inj (oldLive.symm.trans physical.live))).2
    subst old
    refine ⟨{physical.entry with allocation := updated}, address, live, ?_, ?_, ?_, ?_, pointerAddress, nonnull, ?_⟩
    · rw [addresses]; exact cachedAddress
    · rw [lengthEq, sizeEq]; exact storage
    · rw [lengthEq]; exact addressRoom
    · rw [lengthEq]; exact bounds
    · simpa only [addresses, sizeEq] using provenance
  have edge : Q.precise.completion.parents[Q.pointer.grant.toNat]? = some (some selected.pointer.grant) := by
    rw [pointerQ, completionQ]
    exact witness.edge
  let R : CurrentCallPostEntryCheckpoint.Return post next place := {
    data := nextData, owner := nextOwner, id := physical.id, offset := physical.offset.toNat, window := Rwindow,
    physical := P, physicalId := rfl, physicalOffset := rfl, physicalAllocation := allocationQ.symm,
    binding := finalBinding, original := selected.pointer, originalId := selected.pointerId,
    originalPointer := samePointer.symm, originalIssued := originalIssued,
    originalBinding := by rw [allocationQ]; exact parentBinding, edge := edge,
    runtime := by rw [allocationQ]; exact runtime_mono currentRuntime flags counter,
    distinct := by rw [allocationQ]; exact finalDistinct,
    short := by rw [allocationQ]; exact finalShort,
    node := witness.node, nodeAt := by rw [pointerQ, allocationQ]; exact nodeAtFinal,
    leaf := leaf, hidden := hidden,
    activity := by rw [pointerQ, allocationQ]; exact active,
    profile := ready }
  refine ⟨R, rfl, rfl, rfl, allocationQ, witness.tag, ?_⟩
  rw [allocationQ]
  exact finalGrowth

/-- The LIVE Bool backend returns the common scalar bank on its same actual
protected state. This is also the backend after same-ID source materialization. -/
theorem protect_live (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (machine : Before) (tracker : MachineHooks.BorrowState) (data : Identities) (owner : Nat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker = some tracker) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (W : UniformWindow machine tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer = W.pointer.value) (allocation : physical.entry.allocation = W.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1)
    (distinct : W.allocation.extra.roots.toList.Nodup) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (short : W.allocation.extra.nodes.size + 1 < 65536)
    (ghost : machine.user.payload.ghost = false) (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1) :
    ∃ (output : GeneralBorrowForestFnEntry.Output) (post : RootState),
    ∃ R : CurrentCallPostEntryCheckpoint.Return post.machine ⟨output.global, tracker.retagMode⟩ place,
      (ExecutionMachine.callHooks (config options remaining span) options.limits).protectArgument () place
        (Storage.withCurrent frames frame machine) = .ok () post ∧
      R.id = physical.id ∧ R.offset = physical.offset.toNat ∧ R.original = W.pointer ∧
      R.node.tag = tracker.global.nextPointerTag ∧
      R.window.allocation.extra.nodes.size ≤ W.allocation.extra.nodes.size + 1 ∧
      post.machine.borrowTracker = some ⟨output.global, tracker.retagMode⟩ ∧
      output.global = (GeneralBorrowFnEntryRegistration.registered tracker.global borrowFrame physical.id fresh).1 ∧
      post.stack = (Storage.withCurrent frames (registeredFrame frame borrowFrame physical.id tracker.global.nextPointerTag) machine).stack ∧
      CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame physical.id
        W.pointer.value.provenance physical.offset 1 = .ok output ∧
      R.window.allocation.extra.tagMapping = output.child.tree.tagMapping ∧
      R.window.allocation.extra = (output.child.tree.performBorrowAccessRange (.concrete output.tag)
        (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed).tree ∧
      Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
        ((physical.entry.allocation.setExtra output.child.tree).setExtra
          (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
            .Write output.global.protectedTags .VisitChildrenOfAccessed).tree) = .ok () R.window.allocation ∧
      post.machine = {(ReturnProtection.borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree).machine with
        memory := {(ReturnProtection.borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree).machine.memory with
          live := (((ReturnProtection.borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree).machine.memory.live.filter
            (fun row => row.1 != physical.id)).push (physical.id, {physical.entry with allocation := R.window.allocation}))}} := by
  obtain ⟨output, child, actual, tag, globalEq, _, ⟨witness⟩, updated, protectActual, extra, sizeEq, lengthEq,
      mutable, write, _, tracked, _, _⟩ := CurrentCallSelectedBoolProtection.protect options options.limits remaining span ctx
    machine tracker data owner frames frame borrowFrame enabled frameBorrow place physical W pointer allocation runtime binding
    distinct fresh short ghost race backend ready
  let constructor := ReturnProtection.borrowedState frames frame borrowFrame machine tracker fresh physical.id physical.entry output.child.tree
  let post : RootState := {constructor with machine := {constructor.machine with memory := {constructor.machine.memory with live :=
    ((constructor.machine.memory.live.filter (fun row => row.1 != physical.id)).push
      (physical.id, {physical.entry with allocation := updated}))}}}
  have constructorPresent : Present (ActualWorld constructor.machine) physical.id (W.allocation.setExtra output.child.tree) := by
    simp only [Present, ActualWorld, Array.toList_map]
    apply List.mem_map.mpr
    refine ⟨(physical.id, {physical.entry with allocation := physical.entry.allocation.setExtra output.child.tree}), ?_, ?_⟩
    · exact Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inr rfl))
    · rw [allocation]
  have postLive : post.machine.memory.live.find? (fun row => row.1 == physical.id) =
      some (physical.id, {physical.entry with allocation := updated}) := MemoryCopyBridge.live_lookup_replaced _ _ _
  have rootTag : output.global.rootTag? physical.id = tracker.global.rootTag? physical.id := by rw [globalEq]; rfl
  have extraSelected : updated.extra = (output.child.tree.performBorrowAccessRange (.concrete output.tag)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed).tree := by
    rw [tag, globalEq]
    exact extra
  have writeSelected : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
      ((physical.entry.allocation.setExtra output.child.tree).setExtra
        (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
          .Write output.global.protectedTags .VisitChildrenOfAccessed).tree) = .ok () updated := by
    rw [tag, globalEq]
    exact write
  have postReady : CurrentCallBoolProtection.WindowReady post.machine physical.id physical.offset.toNat 1 :=
    CurrentCallBoolProtection.WindowReady.transport ready rfl
  obtain ⟨R, idEq, offsetEq, original, allocationR, nodeTag, growth⟩ := return_view physical W pointer allocation runtime binding distinct
    borrowFrame fresh short output child actual witness tag constructor.machine constructorPresent rootTag post.machine updated postLive
    rfl postReady sizeEq lengthEq mutable extraSelected writeSelected ⟨output.global, tracker.retagMode⟩ rfl (Nat.le_refl _)
    (fun _ hit => hit)
  have tags := (CurrentCallSelectedBoolCurrent.operation_runtime W runtime borrowFrame fresh distinct short
    physical.offset rfl output child actual witness tag constructor.machine constructorPresent rootTag .VisitChildrenOfAccessed).2.2.2.2.2.2.1
  refine ⟨output, post, R, protectActual, idEq, offsetEq, original, nodeTag.trans tag, growth, ?_, globalEq, rfl, actual, ?_, ?_, ?_, ?_⟩
  · change constructor.machine.borrowTracker = _
    rw [tracked, globalEq]
    rfl
  · rw [allocationR, extraSelected]
    exact tags
  · rw [allocationR]
    exact extraSelected
  · rw [allocationR]
    exact writeSelected
  · rw [allocationR]

/-- The actual typed retag continuation writes the Bool and builds the common
return certificate. The selected view is technical; the constructor state is
exactly the state returned by the real retag, including conversion effects. -/
theorem protect_of_retag (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (initial : RootState) (tracker : MachineHooks.BorrowState)
    (enabled : initial.machine.borrowTracker = some tracker)
    (view : Before) (data : Identities) (owner : Nat) (place : MPlaceTy Provenance)
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow view place)
    (W : UniformWindow view tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer = W.pointer.value) (allocation : physical.entry.allocation = W.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding view physical.pointer physical.id physical.offset.toNat 1)
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (borrowFrame : FrameState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (short : W.allocation.extra.nodes.size + 1 < 65536)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame physical.id
      W.pointer.value.provenance physical.offset 1 = .ok output)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child physical.offset 1)
    (tag : output.tag = tracker.global.nextPointerTag)
    (constructor : RootState) (next : MachineHooks.BorrowState)
    (retagActual : TypedRetag.retagPlace (config options remaining span).retag options.limits.retag place
      MachineHooks.protectionPolicy initial = .ok (TypedRetagGeneric.retaggedPlace place physical.id output.tag) constructor)
    (constructorPhysical : CandidateCurrentBoolUninitWrite.PhysicalWindow constructor.machine
      (TypedRetagGeneric.retaggedPlace place physical.id output.tag))
    (idEq : constructorPhysical.id = physical.id) (offsetEq : constructorPhysical.offset = physical.offset)
    (entryEq : constructorPhysical.entry = {physical.entry with allocation := physical.entry.allocation.setExtra output.child.tree})
    (concrete : constructorPhysical.pointer.provenance = .concrete constructorPhysical.id output.tag)
    (tracked : constructor.machine.borrowTracker = some next)
    (flags : next.global.protectedTags = output.global.protectedTags)
    (counter : output.global.nextPointerTag.value.toNat ≤ next.global.nextPointerTag.value.toNat)
    (rootTag : output.global.rootTag? physical.id = tracker.global.rootTag? physical.id)
    (rootHit : ∀ tag, output.global.rootTag? physical.id = some tag → next.global.rootTag? physical.id = some tag)
    (addresses : constructor.machine.user.addresses = view.user.addresses)
    (ghost : constructor.machine.user.payload.ghost = false) (race : constructor.machine.dataRace = none)
    (backend : constructor.machine.user.payload.payload.user.backend = .none)
    (ready : CurrentCallBoolProtection.WindowReady constructor.machine physical.id physical.offset.toNat 1) :
    ∃ post : RootState, ∃ R : CurrentCallPostEntryCheckpoint.Return post.machine next place,
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag options.limits.retag place initial = .ok () post ∧
      R.id = physical.id ∧ R.offset = physical.offset.toNat ∧ R.original = W.pointer ∧
      R.node.tag = output.tag ∧ R.window.allocation.extra.nodes.size ≤ W.allocation.extra.nodes.size + 1 ∧
      post.machine.borrowTracker = some next ∧ post.stack = constructor.stack ∧
      post.machine = {constructor.machine with memory := {constructor.machine.memory with live :=
        ((constructor.machine.memory.live.filter (fun row => row.1 != physical.id)).push
          (physical.id, {physical.entry with allocation := R.window.allocation}))}} := by
  have present : Present (ActualWorld constructor.machine) physical.id (W.allocation.setExtra output.child.tree) := by
    have live := constructorPhysical.live
    rw [idEq, entryEq, allocation] at live
    simp only [Present, ActualWorld, Array.toList_map]
    exact List.mem_map.mpr ⟨_, Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live), rfl⟩
  have done := (CurrentCallSelectedBoolCurrent.operation_runtime W runtime borrowFrame fresh distinct short
    physical.offset rfl output child actual witness tag constructor.machine present rootTag .VisitChildrenOfAccessed).1
  have completed : (constructorPhysical.entry.allocation.extra.performBorrowAccessRange (.concrete output.tag)
      (Size.ofBytes constructorPhysical.offset) (Size.ofBytes 1) .Write next.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    rw [entryEq, offsetEq, flags]
    exact done
  obtain ⟨sync, extras, outside⟩ := ready
  have extras' : constructor.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == constructorPhysical.id) =
      some (constructorPhysical.id, ⟨none, sync⟩) := by rw [idEq]; exact extras
  obtain ⟨updated, writeActual, extra, sizeEq, lengthEq, mutable, write⟩ :=
    CurrentCallBoolProtection.write_uninit_concrete options remaining span ctx constructor _ constructorPhysical next tracked
      output.tag concrete ghost race backend sync extras' (by simpa only [offsetEq] using outside) completed
  let post : RootState := {constructor with machine := {constructor.machine with memory := {constructor.machine.memory with live :=
    ((constructor.machine.memory.live.filter (fun row => row.1 != constructorPhysical.id)).push
      (constructorPhysical.id, {constructorPhysical.entry with allocation := updated}))}}}
  have protectActual : TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag options.limits.retag place initial = .ok () post := by
    unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
    simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, EStateM.pure, enabled, Option.isSome_some, ite_true, retagActual]
    exact writeActual
  have postLive : post.machine.memory.live.find? (fun row => row.1 == physical.id) =
      some (physical.id, {physical.entry with allocation := updated}) := by
    dsimp only [post]
    rw [idEq, entryEq]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have extraSelected : updated.extra = (output.child.tree.performBorrowAccessRange (.concrete output.tag)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed).tree := by
    simpa only [entryEq, offsetEq, flags, Allocation.setExtra, Allocation.mapExtra] using extra
  have writeSelected : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
      ((physical.entry.allocation.setExtra output.child.tree).setExtra
        (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
          .Write output.global.protectedTags .VisitChildrenOfAccessed).tree) = .ok () updated := by
    simpa only [entryEq, offsetEq, flags, Allocation.setExtra, Allocation.mapExtra] using write
  have postReady : CurrentCallBoolProtection.WindowReady post.machine physical.id physical.offset.toNat 1 :=
    ⟨sync, extras, outside⟩
  obtain ⟨R, rId, rOffset, original, allocationR, nodeTag, growth⟩ := return_view physical W pointer allocation runtime binding distinct
    borrowFrame fresh short output child actual witness tag constructor.machine present rootTag post.machine updated postLive
    addresses postReady (by rw [entryEq] at sizeEq; exact sizeEq)
    (by rw [entryEq] at lengthEq; exact lengthEq) mutable extraSelected writeSelected next flags counter rootHit
  refine ⟨post, R, protectActual, rId, rOffset, original, nodeTag, growth, tracked, rfl, ?_⟩
  dsimp only [post]
  rw [allocationR, idEq, entryEq]

private theorem constructor_physical {view : Before} {place : MPlaceTy Provenance}
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow view place)
    (constructor : Before) (tree : BorrowTree) (tag : BorTag)
    (live : constructor.memory.live.find? (fun row => row.1 == physical.id) =
      some (physical.id, {physical.entry with allocation := physical.entry.allocation.setExtra tree}))
    (addresses : constructor.user.addresses = view.user.addresses) :
    ∃ P : CandidateCurrentBoolUninitWrite.PhysicalWindow constructor
        (TypedRetagGeneric.retaggedPlace place physical.id tag),
      P.id = physical.id ∧ P.offset = physical.offset ∧
      P.entry = {physical.entry with allocation := physical.entry.allocation.setExtra tree} ∧
      P.pointer.provenance = .concrete P.id tag := by
  let pointer : Pointer Provenance := {physical.pointer with provenance := .concrete physical.id tag}
  let P : CandidateCurrentBoolUninitWrite.PhysicalWindow constructor
      (TypedRetagGeneric.retaggedPlace place physical.id tag) := {
    pointer := pointer,
    physicalPointer := by
      change Pointer.new (some (Provenance.concrete physical.id tag)) place.mplace.ptr.offset = _
      rw [congrArg (fun p : Pointer (Option Provenance) => p.offset) physical.physicalPointer]
      rfl,
    layout := physical.layout, aligned := physical.aligned,
    id := physical.id, entry := {physical.entry with allocation := physical.entry.allocation.setExtra tree},
    base := physical.base, offset := physical.offset, capacity := physical.capacity,
    live := live, cachedBase := by rw [addresses]; exact physical.cachedBase,
    pointerAddress := physical.pointerAddress, bounds := physical.bounds,
    size := physical.size, bytes := physical.bytes, mutable := physical.mutable,
    maskValid := physical.maskValid, maskLength := physical.maskLength, provenanceMap := physical.provenanceMap }
  exact ⟨P, rfl, rfl, rfl, rfl⟩

theorem protect (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (initial : RootState) (tracker : MachineHooks.BorrowState)
    (enabled : initial.machine.borrowTracker = some tracker)
    (view : Before) (data : Identities) (owner : Nat) (place : MPlaceTy Provenance)
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow view place)
    (W : UniformWindow view tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer = W.pointer.value) (allocation : physical.entry.allocation = W.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding view physical.pointer physical.id physical.offset.toNat 1)
    (distinct : W.allocation.extra.roots.toList.Nodup)
    (borrowFrame : FrameState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (short : W.allocation.extra.nodes.size + 1 < 65536)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex)
    (actual : CandidateCurrentFnEntryRaw.operation W.allocation.extra tracker.global borrowFrame physical.id
      W.pointer.value.provenance physical.offset 1 = .ok output)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child physical.offset 1)
    (tag : output.tag = tracker.global.nextPointerTag)
    (constructor : RootState) (next : MachineHooks.BorrowState)
    (retagActual : TypedRetag.retagPlace (config options remaining span).retag options.limits.retag place
      MachineHooks.protectionPolicy initial = .ok (TypedRetagGeneric.retaggedPlace place physical.id output.tag) constructor)
    (constructorLive : constructor.machine.memory.live.find? (fun row => row.1 == physical.id) =
      some (physical.id, {physical.entry with allocation := physical.entry.allocation.setExtra output.child.tree}))
    (tracked : constructor.machine.borrowTracker = some next)
    (flags : next.global.protectedTags = output.global.protectedTags)
    (counter : output.global.nextPointerTag.value.toNat ≤ next.global.nextPointerTag.value.toNat)
    (rootTag : output.global.rootTag? physical.id = tracker.global.rootTag? physical.id)
    (rootHit : ∀ tag, output.global.rootTag? physical.id = some tag → next.global.rootTag? physical.id = some tag)
    (addresses : constructor.machine.user.addresses = view.user.addresses)
    (ghost : constructor.machine.user.payload.ghost = false) (race : constructor.machine.dataRace = none)
    (backend : constructor.machine.user.payload.payload.user.backend = .none)
    (ready : CurrentCallBoolProtection.WindowReady constructor.machine physical.id physical.offset.toNat 1) :
    ∃ post : RootState, ∃ R : CurrentCallPostEntryCheckpoint.Return post.machine next place,
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag options.limits.retag place initial = .ok () post ∧
      R.id = physical.id ∧ R.offset = physical.offset.toNat ∧ R.original = W.pointer ∧
      R.node.tag = output.tag ∧ R.window.allocation.extra.nodes.size ≤ W.allocation.extra.nodes.size + 1 ∧
      post.machine.borrowTracker = some next ∧ post.stack = constructor.stack ∧
      post.machine = {constructor.machine with memory := {constructor.machine.memory with live :=
        ((constructor.machine.memory.live.filter (fun row => row.1 != physical.id)).push
          (physical.id, {physical.entry with allocation := R.window.allocation}))}} := by
  obtain ⟨P, idEq, offsetEq, entryEq, concrete⟩ := constructor_physical physical constructor.machine output.child.tree output.tag
    constructorLive addresses
  exact protect_of_retag options remaining span ctx initial tracker enabled view data owner place physical W pointer allocation
    runtime binding distinct borrowFrame fresh short output child actual witness tag constructor next retagActual P idEq offsetEq
    entryEq concrete tracked flags counter rootTag rootHit addresses ghost race backend ready

/-- Arbitrary finite CURRENT conversion followed by the real Bool retag and
uninitializing write, with the common return bank on that same final machine. -/
theorem latent (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (machine : Before) (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (family : CurrentCallSpatialCover.Family) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (base offset : UInt64) (place : MPlaceTy Provenance)
    (value : family.value = Pointer.new (.concrete family.allocation root) (Size.ofBytes (base + offset)))
    (physicalPointer : place.mplace.ptr = family.value.withOptionalProvenance)
    (layout : place.layout = RootCompilerFacts.boolLayout) (aligned : place.mplace.misaligned = none)
    (physicalSource : Physical source offset 1 false)
    (current : CurrentPayload machine family.allocation source)
    (absent : machine.memory.live.find? (fun row => row.1 == family.allocation) = none)
    (noFunction : machine.memory.hasFunctionPointer family.allocation = false)
    (noVaList : machine.memory.hasVaListId family.allocation = false)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == family.allocation) = some ⟨family.allocation, base⟩)
    (rootCached : tracker.global.rootTag? family.allocation = some root)
    (addressRoom : base.toNat + source.len < 2^64) (nonnull : base + offset ≠ 0)
    (rootBelow : root.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (protectors : ∀ row ∈ tracker.global.protectedTags.entries, row.1.value.toNat < tracker.global.nextPointerTag.value.toNat)
    (converted : Allocation Provenance Unit) (attributes : GlobalAllocationAttributes.Attributes source converted)
    (convertedWF : ProvenanceCopy.WellFormed converted.provenanceMap converted.len)
    (after : Before) (afterTracker : MachineHooks.BorrowState)
    (conversion : Allocation.adjustFromTcx source PreparedReflection.actual.compiler.runtime.target.base
      (fun _ _ state => .ok (AllocationCopy.snapshot source) state)
      (CurrentCallConversionActualEnsure.hooks options).rootPointer
      (registeredState frames frame borrowFrame (allocatedMachine machine tracker fresh)
        (allocatedTracker tracker fresh) family.allocation tracker.global.nextPointerTag).machine = .ok converted after)
    (afterEnabled : after.borrowTracker = some afterTracker)
    (afterRoot : afterTracker.global.rootTag? family.allocation = some root)
    (afterCached : after.user.addresses.baseAddr.find? (fun row => row.allocId == family.allocation) = some ⟨family.allocation, base⟩)
    (afterRace : after.dataRace = none) (afterGhost : after.user.payload.ghost = false)
    (afterBackend : after.user.payload.payload.user.backend = .none)
    (afterExtras : after.user.payload.payload.user.runtime.extras.allocations.any (fun row => row.1 == family.allocation) = false)
    (flags : afterTracker.global.protectedTags = (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags)
    (counter : (allocatedTracker tracker fresh).global.nextPointerTag.value.toNat ≤ afterTracker.global.nextPointerTag.value.toNat) :
    ∃ post : RootState, ∃ R : CurrentCallPostEntryCheckpoint.Return post.machine afterTracker place,
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag options.limits.retag place
        (Storage.withCurrent frames frame machine) = .ok () post ∧
      R.id = family.allocation ∧ R.offset = offset.toNat ∧ R.original = family.at allocationRoot ∧
      R.node.tag = tracker.global.nextPointerTag ∧ R.window.allocation.extra.nodes.size ≤ 2 ∧
      post.machine.borrowTracker = some afterTracker ∧
      post.stack = (Storage.withCurrent frames (registeredFrame frame borrowFrame family.allocation tracker.global.nextPointerTag) machine).stack ∧
      post.machine = {childMachine options after family.allocation root tracker.global.nextPointerTag converted
          afterTracker.global.protectedTags offset 1 with memory :=
        {(childMachine options after family.allocation root tracker.global.nextPointerTag converted
          afterTracker.global.protectedTags offset 1).memory with live :=
          (((childMachine options after family.allocation root tracker.global.nextPointerTag converted
            afterTracker.global.protectedTags offset 1).memory.live.filter (fun row => row.1 != family.allocation)).push
            (family.allocation, ⟨.machine .global, R.window.allocation⟩))}} := by
  have bounds : offset.toNat + 1 ≤ source.byteSize.bytes.toNat := by
    simpa only [UInt64.toNat_one] using physicalSource.2.2.1
  have ptr : place.mplace.ptr = Pointer.new (some (.concrete family.allocation root)) (Size.ofBytes (base + offset)) := by
    rw [physicalPointer, value]; rfl
  have actualRetag := retag options remaining span ctx frames frame borrowFrame frameBorrow machine tracker enabled fresh
    family.allocation root source base offset place ptr layout current absent noFunction noVaList cached bounds rootBelow protectors
    converted attributes after afterTracker conversion afterEnabled afterRoot afterRace afterExtras flags
  let view := {rootMachine options after family.allocation root converted with borrowTracker := some tracker}
  have live : view.memory.live.find? (fun row => row.1 == family.allocation) =
      some (family.allocation, ⟨.machine .global, converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)⟩) := by
    rw [← attributes.size]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  obtain ⟨_, _, _, _, P, idEq, pointerEq, allocationEq, offsetEq, W, wPointer, wAllocation⟩ :=
    root_view view tracker family root source converted attributes convertedWF base offset place value physicalPointer layout aligned
      physicalSource live afterCached rootCached addressRoom nonnull rootBelow protectors
  have samePointer : P.pointer = W.pointer.value := by rw [pointerEq, wPointer]; rfl
  have sameAllocation : P.entry.allocation = W.allocation := allocationEq.trans wAllocation.symm
  have run : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global := by
    rw [wAllocation]
    exact (root_view view tracker family root source converted attributes convertedWF base offset place value physicalPointer layout aligned
      physicalSource live afterCached rootCached addressRoom nonnull rootBelow protectors).2.1
  have bind : CandidateCallBindings.WindowBinding view P.pointer P.id P.offset.toNat 1 := by
    rw [pointerEq, idEq, offsetEq]
    exact (root_view view tracker family root source converted attributes convertedWF base offset place value physicalPointer layout aligned
      physicalSource live afterCached rootCached addressRoom nonnull rootBelow protectors).2.2.1
  have distinct : W.allocation.extra.roots.toList.Nodup := by rw [wAllocation]; change ([allocationRoot] : List UniIndex).Nodup; simp
  have short : W.allocation.extra.nodes.size + 1 < 65536 := by rw [wAllocation]; change 2 < 65536; decide
  have treeBounds : P.offset.toNat + 1 ≤ W.allocation.extra.locations.size.bytes.toNat := by
    rw [wAllocation, offsetEq]
    have nonzero : source.byteSize.bytes ≠ 0 := by
      intro zero
      rw [zero] at bounds
      simp only [UInt64.toNat_zero] at bounds
      omega
    change offset.toNat + 1 ≤ (BorrowTree.new root (Size.ofBytes source.byteSize.bytes)).locations.size.bytes.toNat
    have shape := tree_eq source.byteSize.bytes nonzero root
    change BorrowTree.new root (Size.ofBytes source.byteSize.bytes) = _ at shape
    rw [shape]
    exact bounds
  obtain ⟨output, child, actual, tag, globalEq, _, _, _, _, ⟨witness⟩⟩ :=
    CurrentCallResourceFnEntry.correlated_borrow_selected W run borrowFrame fresh rfl distinct (by omega) (by omega)
      P.offset 1 rfl rfl (by decide) treeBounds
  have literalEq : output = CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global borrowFrame P.id fresh
      W.pointer.value.provenance P.offset 1 :=
    Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ fresh _ _ _))
  have childTree : output.child.tree = PositiveGlobalTypedReborrow.finalTree root tracker.global.nextPointerTag converted.byteSize
      afterTracker.global.protectedTags offset 1 := by
    rw [literalEq, wAllocation, wPointer, offsetEq]
    change (CurrentCallTypedFnEntry.literal (BorrowTree.new root source.byteSize) tracker.global borrowFrame P.id fresh
      family.value.provenance offset 1).child.tree = _
    rw [value, attributes.size, flags]
    rfl
  have entryEq : P.entry = ⟨.machine .global, converted.mapExtra (fun _ => BorrowTree.new root source.byteSize)⟩ := by
    have pLive := P.live
    rw [idEq, live] at pLive
    exact (Prod.mk.inj (Option.some.inj pLive)).2.symm
  let constructor := Storage.withCurrent frames (registeredFrame frame borrowFrame family.allocation tracker.global.nextPointerTag)
    (childMachine options after family.allocation root tracker.global.nextPointerTag converted afterTracker.global.protectedTags offset 1)
  have ctorLive : constructor.machine.memory.live.find? (fun row => row.1 == P.id) =
      some (P.id, {P.entry with allocation := P.entry.allocation.setExtra output.child.tree}) := by
    rw [idEq, entryEq, childTree]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have rootTag : output.global.rootTag? P.id = tracker.global.rootTag? P.id := by rw [globalEq]; rfl
  have rootHit : ∀ tag, output.global.rootTag? P.id = some tag → afterTracker.global.rootTag? P.id = some tag := by
    intro tag hit
    rw [rootTag, idEq, rootCached] at hit
    cases Option.some.inj hit
    rw [idEq]
    exact afterRoot
  have ready : CurrentCallBoolProtection.WindowReady constructor.machine P.id P.offset.toNat 1 := by
    rw [idEq]
    refine ⟨#[], ?_, by simp⟩
    change (((after.user.payload.payload.user.runtime.extras.allocations.filter (fun row => row.1 != family.allocation)).push
      (family.allocation, ⟨none, #[]⟩)).find? (fun row => row.1 == family.allocation)) = _
    have noMatch : (fun row : AllocId × MemoryExtras.AllocationExtra Unit =>
        decide ((row.1 != family.allocation) = true ∧ (row.1 == family.allocation) = true)) = (fun _ => false) := by
      funext row
      by_cases equal : row.1 = family.allocation <;> simp [equal]
    have emptyFind : after.user.payload.payload.user.runtime.extras.allocations.find? (fun _ => false) = none := by
      simp [Array.find?_eq_none]
    simp [Array.find?_push, Array.find?_filter, noMatch, emptyFind]
  have retag' : TypedRetag.retagPlace (config options remaining span).retag options.limits.retag place MachineHooks.protectionPolicy
      (Storage.withCurrent frames frame machine) = .ok (TypedRetagGeneric.retaggedPlace place P.id output.tag) constructor := by
    simpa only [idEq, tag, constructor] using actualRetag
  obtain ⟨post, R, completed, rId, rOffset, original, nodeTag, growth, tracked, stack, machineEq⟩ :=
    protect options remaining span ctx (Storage.withCurrent frames frame machine) tracker enabled view _ _ place P W
      samePointer sameAllocation run bind distinct borrowFrame fresh short output child actual witness tag constructor afterTracker retag'
      ctorLive afterEnabled (by rw [globalEq]; exact flags) (by rw [globalEq]; exact counter) rootTag rootHit rfl
      afterGhost afterRace afterBackend ready
  refine ⟨post, R, completed, rId.trans idEq, rOffset.trans (congrArg UInt64.toNat offsetEq), original.trans wPointer,
    nodeTag.trans tag, ?_, tracked, stack, ?_⟩
  · rw [wAllocation] at growth
    exact growth
  · simpa only [constructor, Storage.withCurrent, idEq, entryEq] using machineEq

end DuplicatePrefix.CurrentCallConversionBool
