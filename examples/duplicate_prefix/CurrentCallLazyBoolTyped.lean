import duplicate_prefix.CurrentCallLazyBoolEnsure
import duplicate_prefix.PositiveGlobalTypedReborrow
import duplicate_prefix.CurrentCallSelectedBoolWindow
import duplicate_prefix.CurrentCallSelectedBoolProtection
import duplicate_prefix.CurrentCallPostEntryCheckpoint
import duplicate_prefix.S03UninitProvenance

/-! Actual latent Bool retagging. Protector registration precedes the one real
ensure; no materialized prestate is substituted for the original call state. -/
namespace DuplicatePrefix.CurrentCallLazyBoolTyped
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
open CurrentCallLazyBoolEnsure
open TypedRetagEntry GeneralBorrowFullSharedSeed GeneralRangeMapOrigins
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallFamilySatisfaction
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The ensure-ready facts hold at their real phase, after the child's fresh
tag and protector have been installed. This changes no memory/address data. -/
theorem registered_ready (options : EvalConfigurationCore.Options)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (machine : Before) (tracker : MachineHooks.BorrowState)
    (family : CurrentCallSpatialCover.Family) (root : BorTag)
    (source : Allocation CtfeProvenance Unit) (base offset : UInt64) (place : MPlaceTy Provenance)
    (ready : Ready options (Storage.withCurrent frames frame machine) tracker family root source base offset place)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615) :
    Ready options (registeredState frames frame borrowFrame (allocatedMachine machine tracker fresh)
      (allocatedTracker tracker fresh) family.allocation tracker.global.nextPointerTag)
      (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag)
      family root source base offset place := by
  have step : (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat=
      tracker.global.nextPointerTag.value.toNat+1 := by
    have bound : tracker.global.nextPointerTag.value.toNat<18446744073709551615 := by
      simpa [UInt64.lt_iff_toNat_lt] using fresh
    change (tracker.global.nextPointerTag.value+1).toNat=_
    rw [UInt64.toNat_add,UInt64.toNat_one,Nat.mod_eq_of_lt (by omega)]
  refine {ready with enabled:=rfl,rootBelow:=?_,protectors:=?_}
  · change root.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
    rw [step]
    exact Nat.lt_trans ready.rootBelow (Nat.lt_succ_self _)
  · intro row member
    change row∈(tracker.global.protectedTags.entries.filter (fun entry=>entry.1!=tracker.global.nextPointerTag)).push
      (tracker.global.nextPointerTag,.StrongProtector) at member
    change row.1.value.toNat<(TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat
    rw [step]
    rcases Array.mem_push.mp member with old | same
    · exact Nat.lt_trans (ready.protectors row (Array.mem_filter.mp old).1) (Nat.lt_succ_self _)
    · subst row
      exact Nat.lt_succ_self _

private theorem seeded_view (options : EvalConfigurationCore.Options) (before : RootState) (tracker : MachineHooks.BorrowState)
    (family : Family) (root : BorTag) (source : Allocation CtfeProvenance Unit) (base offset : UInt64)
    (place : MPlaceTy Provenance) (ready : Ready options before tracker family root source base offset place)
    (converted : Allocation Provenance Unit) (facts : GlobalDataOnlyConversion.Facts source converted) :
    let allocation:=converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)
    let after:=GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options) before.machine family.allocation .global allocation
    AllocationCapability after tracker family.allocation allocation ∧
    DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global ∧
    CandidateCallBindings.WindowBinding after family.value family.allocation offset.toNat 1 ∧
    Satisfies tracker family allocation (Window family.allocation offset.toNat 1) ∧
    ∃physical : CandidateCurrentBoolUninitWrite.PhysicalWindow after place,
      physical.id=family.allocation ∧physical.pointer=family.value ∧physical.entry.allocation=allocation ∧physical.offset=offset ∧
    ∃B : UniformWindow after tracker (identities family (completion root source.byteSize)) 0 family.allocation offset.toNat 1 .ret,
      B.pointer=family.at allocationRoot ∧B.allocation=allocation := by
  let allocation:=converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)
  let after:=GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options) before.machine family.allocation .global allocation
  have live : after.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,⟨.machine .global,allocation⟩):=
    MemoryCopyBridge.live_lookup_replaced before.machine.memory family.allocation _
  have nonzero : source.byteSize.bytes≠0:=by
    intro zero
    have bounds:=ready.bounds
    rw [zero] at bounds
    simp only [UInt64.toNat_zero] at bounds
    omega
  have shape:=tree_eq source.byteSize.bytes nonzero root
  change BorrowTree.new root (Size.ofBytes source.byteSize.bytes)=_ at shape
  have length : allocation.len=allocation.byteSize.bytes.toNat:=by
    change converted.len=converted.byteSize.bytes.toNat
    rw [facts.storage,facts.size]
    exact ready.storage
  have treeSize : allocation.extra.locations.size=allocation.byteSize:=by
    change (BorrowTree.new root source.byteSize).locations.size=converted.byteSize
    rw [facts.size]
    exact (by rw [show source.byteSize=Size.ofBytes source.byteSize.bytes from rfl,shape];rfl)
  have cap : AllocationCapability after tracker family.allocation allocation:=by
    refine ⟨?_,length,treeSize,rfl,_,BorrowTree.new_root_node _ _,rfl,rfl,ready.rootCached⟩
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(family.allocation,⟨.machine .global,allocation⟩),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
  have runtime : DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global:=
    S03MaterializableRootRuntime.initial root source.byteSize.bytes tracker.global ready.rootBelow ready.protectors
  have parents : ParentInterpretation allocation.extra (completion root source.byteSize):=by
    exact ((positive_global_rule ".CurrentCallLazyBoolEnsure.rootChain") root source.byteSize).parents runtime.formed.toGraphState
      (GeneralBorrowParentTagRootFrames.new_root root source.byteSize) (by change ([allocationRoot] : List UniIndex).Nodup;simp)
      _ (BorrowTree.new_root_node root source.byteSize) rfl
  have pointerBind : PointerBinds allocation (family.at allocationRoot):=by
    refine ⟨_,BorrowTree.new_root_node _ _,runtime.formed.allocator.nodeTags _ _ (BorrowTree.new_root_node _ _),?_⟩
    change (match family.value.provenance with | .concrete id tag=>id=family.allocation ∧tag=root | .wildcard=>false=true)
    rw [ready.value]
    exact ⟨rfl,rfl⟩
  have offsetBound : offset.toNat≤source.len:=by have bounds:=ready.bounds;rw [ready.storage];omega
  have sumFits : base.toNat+offset.toNat<2^64:=by have room:=ready.addressRoom;omega
  have binding : CandidateCallBindings.WindowBinding after family.value family.allocation offset.toNat 1:=by
    refine ⟨⟨.machine .global,allocation⟩,base,live,ready.cached,length,?_,?_,?_,?_,?_⟩
    · change base.toNat+converted.len<2^64
      rw [facts.storage]
      exact ready.addressRoom
    · change offset.toNat+1≤converted.len
      rw [facts.storage,ready.storage]
      exact ready.bounds
    · rw [ready.value]
      change (base+offset).toNat=base.toNat+offset.toNat
      rw [UInt64.toNat_add,Nat.mod_eq_of_lt sumFits]
    · rw [ready.value]
      exact ready.nonnull
    · rw [ready.value]
      rfl
  let physical : CandidateCurrentBoolUninitWrite.PhysicalWindow after place:={
    pointer:=family.value,physicalPointer:=ready.physicalPointer,layout:=ready.layout,aligned:=ready.aligned,
    id:=family.allocation,entry:=⟨.machine .global,allocation⟩,base:=base,offset:=offset,capacity:=source.byteSize.bytes,
    live:=live,cachedBase:=ready.cached,pointerAddress:=by rw [ready.value];rfl,
    bounds:=ready.bounds,size:=facts.size,bytes:=by change converted.len=source.byteSize.bytes.toNat;rw [facts.storage,ready.storage],
    mutable:=facts.mutability.trans ready.mutable,
    maskValid:=by change InitMaskCopy.WellFormed converted.initializationMask;rw [facts.mask];exact ready.maskValid,
    maskLength:=by change converted.initializationMask.len=Size.ofBytes source.byteSize.bytes;rw [facts.mask];exact ready.maskLength,
    provenanceMap:=by
      change ProvenanceCopy.WellFormed converted.provenanceMap converted.len
      rw [facts.provenance]
      constructor <;> simp [ProvenanceMap.new,ProvenanceCopy.FragmentsAvoidPointers]}
  let B : UniformWindow after tracker (identities family (completion root source.byteSize)) 0 family.allocation offset.toNat 1 .ret:={
    loan:=⟨0,none,0⟩,pointer:=family.at allocationRoot,allocation:=allocation,precise:=⟨completion root source.byteSize,#[]⟩,
    loanAt:=rfl,pointerAt:=rfl,pointerId:=rfl,present:=cap.live,preciseAt:=by simp [identities],
    binding:=pointerBind,issued:=.allocated cap,parents:=parents,
    window:=by
      intro byte hit
      refine ⟨?_,(positive_global_rule ".CurrentCallLazyBoolEnsure.seed_embeds") allocation source.byteSize.bytes root nonzero rfl tracker.global.protectedTags _ byte.2⟩
      change byte.2<converted.len
      rw [facts.storage,ready.storage]
      have bound:=ready.bounds
      have upper:=hit.2.2
      omega}
  have owned : Satisfies tracker family allocation (Window family.allocation offset.toNat 1):=by
    intro byte hit
    obtain ⟨chain,_,support⟩:=CurrentCallSupportChainExtraction.extract_support B.parents B.issued (B.window byte hit).2
    exact ⟨hit.1,allocationRoot,chain,pointerBind,support⟩
  exact ⟨cap,runtime,binding,owned,physical,rfl,rfl,rfl,rfl,B,rfl,rfl⟩

/-- The original Bool reborrow, with its actual registration and lazy ensure.
Only initial descriptor/storage/representation facts are inputs. -/
theorem reborrow (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (machine : Before) (tracker : MachineHooks.BorrowState)
    (family : CurrentCallSpatialCover.Family) (root : BorTag)
    (source : Allocation CtfeProvenance Unit) (base offset : UInt64) (place : MPlaceTy Provenance)
    (ready : Ready options (Storage.withCurrent frames frame machine) tracker family root source base offset place)
    (noFunction : machine.memory.hasFunctionPointer family.allocation=false)
    (noVaList : machine.memory.hasVaListId family.allocation=false)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615) :
    ∃converted : Allocation Provenance Unit,GlobalDataOnlyConversion.Facts source converted ∧
    let registered:=registeredState frames frame borrowFrame (allocatedMachine machine tracker fresh)
      (allocatedTracker tracker fresh) family.allocation tracker.global.nextPointerTag
    let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=
      ⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)⟩
    let cached:=GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options)
      registered.machine family.allocation .global entry.allocation
    let tree:=PositiveGlobalTypedReborrow.finalTree root tracker.global.nextPointerTag source.byteSize
      (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags offset 1
    TypedRetag.reborrow (config options remaining span).retag options.limits.retag place (Size.ofBytes 1)
      MachineHooks.protectionPolicy tracker.global.nextPointerTag
      (Storage.withCurrent frames frame (allocatedMachine machine tracker fresh))=
      .ok (some (.concrete family.allocation tracker.global.nextPointerTag))
        {registered with machine:={cached with memory:=RetagEntry.updatedMemory cached.memory family.allocation entry tree}} := by
  let h:=(config options remaining span).retag
  let allocated:=allocatedMachine machine tracker fresh
  let advanced:=allocatedTracker tracker fresh
  let start:=Storage.withCurrent frames frame allocated
  let registered:=registeredState frames frame borrowFrame allocated advanced family.allocation tracker.global.nextPointerTag
  let next:=registeredTracker advanced tracker.global.nextPointerTag
  have registeredReady:=registered_ready options frames frame borrowFrame machine tracker family root source base offset place ready fresh
  obtain ⟨converted,facts,ensure,_,_,_,_,_,_,_⟩:=CurrentCallLazyBoolEnsure.ensure options () remaining span
    registered next family root source base offset place registeredReady
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=
    ⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)⟩
  let cached:=GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options)
    registered.machine family.allocation .global entry.allocation
  have info : machine.memory.getAllocInfo family.allocation=
      .ok ⟨source.byteSize,source.align,.liveData,source.mutability⟩:=
    GlobalDataOnlyMaterialize.alloc_info machine family.allocation source ready.absent noFunction noVaList ready.descriptor
  have pointerEq : place.mplace.ptr=(Pointer.new (some (.concrete family.allocation root)) (Size.ofBytes (base+offset))) := by
    rw [ready.physicalPointer,ready.value];rfl
  have check : h.checkPtrAccess place.mplace.ptr (Size.ofBytes 1) start=.ok () start := by
    rw [ctx.source.check,pointerEq]
    exact (positive_global_rule ".PositiveGlobalTypedReborrow.check_known") ctx.pointers
      (config options remaining span).access start family.allocation root base offset 1 _
      ctx.resolve ctx.arithmetic ready.cached info rfl (by decide) (by decide) ready.bounds
  have resolve : h.resolveAllocation place.mplace.ptr start=
      .ok (some ⟨family.allocation,Size.ofBytes offset,.concrete root⟩) start := by
    rw [ctx.source.resolve,pointerEq]
    exact RetagPointerChecks.resolve_allocation_cached ctx.pointers start family.allocation root base offset ctx.arithmetic ready.cached
  have frozen : h.typeIsFreeze place.layout.ty=pure true := by
    rw [ready.layout];exact ActualRetagContext.bool_freeze options remaining span ctx
  have inside:=TypedRetagPolicyFields.inside_for_policy h options.limits.retag place (Size.ofBytes 1)
    MachineHooks.protectionPolicy ChildBorrow.fnEntryLocation rfl ctx.source.precise frozen
  have log : h.logCreation=(fun _ _ _ _ _=>pure ()):=ctx.source.log
  refine ⟨converted,facts,?_⟩
  change TypedRetag.reborrow h options.limits.retag place (Size.ofBytes 1) MachineHooks.protectionPolicy tracker.global.nextPointerTag start=_
  unfold TypedRetag.reborrow
  simp only [log,check,resolve,bind,EStateM.bind,pure,EStateM.pure,MachineHooks.protectionPolicy]
  rw [current_frame_pushed start frames frame rfl]
  simp only [frameBorrow,bind,EStateM.bind,pure,EStateM.pure]
  unfold_typed ".TypedRetag.tracker"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,start,Storage.withCurrent,allocated,allocatedMachine,
    bind,EStateM.bind,pure,EStateM.pure]
  simp only [GlobalState.addProtector,FrameState.addProtector,modify,modifyGet,MonadStateOf.modifyGet,
    EStateM.modifyGet,MachineHooks.setCurrentFrame,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
    pure,EStateM.pure,set,EStateM.set,Storage.withCurrent,Array.isEmpty_push,Array.pop_push,Bool.false_eq_true,↓reduceIte]
  unfold_typed ".TypedRetag.checked"
  simp only [info,bind,EStateM.bind,pure,EStateM.pure]
  have liveDataSelf : (AllocationKind.liveData != .liveData)=false:=rfl
  simp only [liveDataSelf,Bool.false_eq_true,↓reduceIte]
  erw [inside]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  erw [ensure]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  let parent:=(BorrowTree.new root source.byteSize).performBorrowAccessRange (.concrete root)
    (Size.ofBytes offset) (Size.ofBytes 1) .Read next.global.protectedTags .VisitChildrenOfAccessed
  let child:=parent.tree.newChild (Size.ofBytes offset) (.concrete root) tracker.global.nextPointerTag
    (DedupRangeMap.new (Size.ofBytes 1) ChildBorrow.fnEntryLocation) (.ReservedFrz false) true
  have stages:=(positive_global_rule ".PositiveGlobalTypedReborrow.read_child") root tracker.global.nextPointerTag
    source.byteSize.bytes offset 1 tracker.global.protectedTags (by decide) ready.bounds ready.rootBelow ready.protectors fresh
  have childExact : parent.tree.newChild (Size.ofBytes offset) (.concrete root) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 1) ChildBorrow.fnEntryLocation) MachineHooks.protectionPolicy.outsidePermission
      MachineHooks.protectionPolicy.protector.isSome=⟨child.tree,.ok ()⟩:=
    GeneralBorrowFreshReborrowStages.child_complete _ stages.2
  have present : cached.memory.live.find? (fun row=>row.1==family.allocation)=some (family.allocation,entry):=
    MemoryCopyBridge.live_lookup_replaced _ _ _
  exact (positive_global_rule ".TypedBorrowSteps.read_insert_steps") h frames
    (registeredFrame frame borrowFrame family.allocation tracker.global.nextPointerTag) cached next rfl family.allocation entry
    offset 1 (.concrete root) tracker.global.nextPointerTag ChildBorrow.fnEntryLocation MachineHooks.protectionPolicy
    rfl (by decide) present ready.race parent.tree child.tree rfl stages.1 childExact

def retagged (options : EvalConfigurationCore.Options)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (machine : Before) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) (offset : UInt64) : RootState :=
  let registered:=registeredState frames frame borrowFrame (allocatedMachine machine tracker fresh)
    (allocatedTracker tracker fresh) id tracker.global.nextPointerTag
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=
    ⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)⟩
  let cached:=GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options)
    registered.machine id .global entry.allocation
  let tree:=PositiveGlobalTypedReborrow.finalTree root tracker.global.nextPointerTag source.byteSize
    (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags offset 1
  {registered with machine:={cached with memory:=RetagEntry.updatedMemory cached.memory id entry tree}}

/-- Metadata projection used only to compare the identical post-ensure
continuation. It is not an additional operational materialization. -/
def seeded (options : EvalConfigurationCore.Options) (machine : Before) (id : AllocId)
    (root : BorTag) (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit) : Before :=
  GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options) machine id .global
    (converted.mapExtra (fun _=>BorrowTree.new root source.byteSize))

private theorem retagged_seeded (options : EvalConfigurationCore.Options)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (machine : Before) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) (offset : UInt64) :
    retagged options frames frame borrowFrame machine tracker fresh id root source converted offset=
      ReturnProtection.borrowedState frames frame borrowFrame (seeded options machine id root source converted)
        tracker fresh id ⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)⟩
        (PositiveGlobalTypedReborrow.finalTree root tracker.global.nextPointerTag source.byteSize
          (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags offset 1) := by
  rfl

/-- Full actual retagPlace from the ORIGINAL latent Bool state. This includes
fresh-tag allocation, registration, metadata check, one ensure and child insert. -/
theorem retag (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (machine : Before) (tracker : MachineHooks.BorrowState)
    (family : CurrentCallSpatialCover.Family) (root : BorTag)
    (source : Allocation CtfeProvenance Unit) (base offset : UInt64) (place : MPlaceTy Provenance)
    (ready : Ready options (Storage.withCurrent frames frame machine) tracker family root source base offset place)
    (noFunction : machine.memory.hasFunctionPointer family.allocation=false)
    (noVaList : machine.memory.hasVaListId family.allocation=false)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615) :
    ∃converted : Allocation Provenance Unit,GlobalDataOnlyConversion.Facts source converted ∧
      TypedRetag.retagPlace (config options remaining span).retag options.limits.retag place MachineHooks.protectionPolicy
        (Storage.withCurrent frames frame machine)=
        .ok (TypedRetagGeneric.retaggedPlace place family.allocation tracker.global.nextPointerTag)
          (retagged options frames frame borrowFrame machine tracker fresh family.allocation root source converted offset) := by
  obtain ⟨converted,facts,actual⟩:=reborrow options remaining span ctx frames frame borrowFrame frameBorrow machine tracker
    family root source base offset place ready noFunction noVaList fresh
  refine ⟨converted,facts,?_⟩
  exact retag_place_of_reborrow (config options remaining span).retag options.limits.retag place MachineHooks.protectionPolicy
    (Size.ofBytes 1) Align.ONE (Storage.withCurrent frames frame machine)
    (retagged options frames frame borrowFrame machine tracker fresh family.allocation root source converted offset)
    tracker ready.enabled fresh family.allocation family.value.provenance (by rw [ready.physicalPointer];rfl)
    (ActualRetagContext.bool_size options remaining span ctx place ready.layout) actual

private theorem protect_same_continuation (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (place nextPlace : MPlaceTy Provenance)
    (before first after : RootState) (leftTracker rightTracker : MachineHooks.BorrowState)
    (leftEnabled : before.machine.borrowTracker=some leftTracker)
    (rightEnabled : first.machine.borrowTracker=some rightTracker)
    (left : TypedRetag.retagPlace (config options remaining span).retag options.limits.retag place MachineHooks.protectionPolicy before=.ok nextPlace after)
    (right : TypedRetag.retagPlace (config options remaining span).retag options.limits.retag place MachineHooks.protectionPolicy first=.ok nextPlace after) :
    TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag options.limits.retag place before=
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag options.limits.retag place first := by
  unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,leftEnabled,rightEnabled,
    Option.isSome_some,ite_true,left,right]

/-- Actual complete Bool protection, including the real writeUninit, from the
original latent state. The output window describes the SAME final allocation;
the temporary technical seeded view is used only to prove the shared suffix. -/
theorem protect (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (machine : Before) (tracker : MachineHooks.BorrowState)
    (family : Family) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (base offset : UInt64) (place : MPlaceTy Provenance)
    (ready : Ready options (Storage.withCurrent frames frame machine) tracker family root source base offset place)
    (noFunction : machine.memory.hasFunctionPointer family.allocation=false)
    (noVaList : machine.memory.hasVaListId family.allocation=false)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (ghost : machine.user.payload.ghost=false) (backend : machine.user.payload.payload.user.backend=.none) :
    ∃post : RootState, ∃data owner,
      ∃Q : UniformWindow post.machine (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag)
        data owner family.allocation offset.toNat 1 .ret,
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag options.limits.retag place
        (Storage.withCurrent frames frame machine)=.ok () post ∧
      post.machine.borrowTracker=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      post.stack=(Storage.withCurrent frames (registeredFrame frame borrowFrame family.allocation tracker.global.nextPointerTag) machine).stack ∧
      DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra
        (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag) ∧
      post.machine.memory.live=(machine.memory.live.filter (fun row=>row.1!=family.allocation)).push
        (family.allocation,⟨.machine .global,Q.allocation⟩) ∧
      post.machine={MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) machine family.allocation ⟨none,#[]⟩ with
        memory:={machine.memory with live:=((machine.memory.live.filter (fun row=>row.1!=family.allocation)).push (family.allocation,⟨.machine .global,Q.allocation⟩))},
        borrowTracker:=some (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag)} ∧
      post.machine.user.addresses=machine.user.addresses ∧
      post.machine.user.payload.payload.user.runtime.extras.allocations=
        (machine.user.payload.payload.user.runtime.extras.allocations.filter (fun row=>row.1!=family.allocation)).push
          (family.allocation,⟨none,#[]⟩) ∧
      SpatialDelegation post.machine (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag)
        family.allocation Q.allocation Q.precise.completion allocationRoot ∧
      PointerBinds Q.allocation (family.at allocationRoot) ∧
      ∃R : CurrentCallPostEntryCheckpoint.Return post.machine
          (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) place,
        R.id=family.allocation ∧R.offset=offset.toNat ∧R.original=family.at allocationRoot ∧R.node.tag=tracker.global.nextPointerTag ∧
        R.window.allocation=Q.allocation ∧R.window.allocation.extra.nodes.size≤2 := by
  obtain ⟨converted,facts,actualRetag⟩:=retag options remaining span ctx frames frame borrowFrame frameBorrow machine tracker
    family root source base offset place ready noFunction noVaList fresh
  let initial:=seeded options machine family.allocation root source converted
  obtain ⟨cap,runtime,binding,_,physical,idEq,pointerEq,allocationEq,offsetEq,B,bPointer,bAllocation⟩:=
    seeded_view options (Storage.withCurrent frames frame machine) tracker family root source base offset place ready converted facts
  change AllocationCapability initial tracker family.allocation _ at cap
  change CandidateCallBindings.WindowBinding initial family.value family.allocation offset.toNat 1 at binding
  change CandidateCurrentBoolUninitWrite.PhysicalWindow initial place at physical
  change UniformWindow initial tracker (identities family (completion root source.byteSize)) 0 family.allocation offset.toNat 1 .ret at B
  have samePointer : physical.pointer=B.pointer.value := by rw [pointerEq,bPointer];rfl
  have sameAllocation : physical.entry.allocation=B.allocation:=allocationEq.trans bAllocation.symm
  have selectedRuntime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global := by rw [bAllocation];exact runtime
  have selectedBinding : CandidateCallBindings.WindowBinding initial physical.pointer physical.id physical.offset.toNat 1 := by
    rw [pointerEq,idEq,offsetEq];exact binding
  let selected : UniformWindow initial tracker (identities family (completion root source.byteSize)) 0
      physical.id physical.offset.toNat 1 .ret := {
    loan:=B.loan,pointer:=B.pointer,allocation:=B.allocation,precise:=B.precise,
    loanAt:=B.loanAt,pointerAt:=B.pointerAt,pointerId:=by rw [idEq];exact B.pointerId,
    present:=by rw [idEq];exact B.present,preciseAt:=by rw [idEq];exact B.preciseAt,
    binding:=B.binding,issued:=by rw [idEq];exact B.issued,parents:=B.parents,
    window:=by intro byte hit;apply B.window;simpa only [idEq,offsetEq] using hit}
  have selectedPointer : physical.pointer=selected.pointer.value:=samePointer
  have selectedAllocation : physical.entry.allocation=selected.allocation:=sameAllocation
  have selectedRun : DuplicatePrefixBorrowContract.RuntimeFacts selected.allocation.extra tracker.global:=selectedRuntime
  have distinct : selected.allocation.extra.roots.toList.Nodup := by
    change B.allocation.extra.roots.toList.Nodup
    rw [bAllocation]
    change ([CurrentCallResourceNormalization.allocationRoot] : List UniIndex).Nodup
    simp
  have short : selected.allocation.extra.nodes.size+1<65536 := by
    change B.allocation.extra.nodes.size+1<65536
    rw [bAllocation]
    change 2<65536
    decide
  have windowReady : CurrentCallBoolProtection.WindowReady initial physical.id physical.offset.toNat 1 := by
    refine ⟨#[],?_,by simp⟩
    rw [idEq]
    change (((machine.user.payload.payload.user.runtime.extras.allocations.filter (fun row=>row.1!=family.allocation)).push
      (family.allocation,⟨none,#[]⟩)).find? (fun row=>row.1==family.allocation))=some (family.allocation,⟨none,#[]⟩)
    have noMatch : (fun row : AllocId × MemoryExtras.AllocationExtra Unit=>
        decide ((row.1!=family.allocation)=true ∧(row.1==family.allocation)=true))=(fun _=>false) := by
      funext row
      by_cases equal : row.1=family.allocation <;> simp [equal]
    have emptyFind : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun _=>false)=none := by
      simp [Array.find?_eq_none]
    simp [Array.find?_push,Array.find?_filter,noMatch,emptyFind]
  obtain ⟨output,child,actual,tag,global,frameEq,⟨witness⟩,updated,protectActual,extra,sizeEq,lengthEq,mutable,write,snapshot,tracked,borrowed,returned⟩:=
    CurrentCallSelectedBoolProtection.protect options options.limits remaining span ctx initial tracker
      (identities family (completion root source.byteSize)) 0 frames frame borrowFrame ready.enabled frameBorrow
      place physical selected selectedPointer selectedAllocation selectedRun selectedBinding distinct fresh short ghost ready.race backend windowReady
  have literalEq : output=CurrentCallTypedFnEntry.literal selected.allocation.extra tracker.global borrowFrame physical.id fresh
      selected.pointer.value.provenance physical.offset 1 :=
    Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ fresh _ _ _))
  have childTree : output.child.tree=PositiveGlobalTypedReborrow.finalTree root tracker.global.nextPointerTag source.byteSize
      (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags offset 1 := by
    rw [literalEq]
    change (CurrentCallTypedFnEntry.literal B.allocation.extra tracker.global borrowFrame physical.id fresh
      B.pointer.value.provenance physical.offset 1).child.tree=_
    rw [bAllocation,bPointer,offsetEq]
    change (CurrentCallTypedFnEntry.literal (BorrowTree.new root source.byteSize) tracker.global borrowFrame physical.id fresh
      family.value.provenance offset 1).child.tree=_
    rw [ready.value]
    rfl
  have stages:=(positive_global_rule ".PositiveGlobalTypedReborrow.read_child") root tracker.global.nextPointerTag
    source.byteSize.bytes offset 1 tracker.global.protectedTags (by decide) ready.bounds ready.rootBelow ready.protectors fresh
  let parent:=(BorrowTree.new root source.byteSize).performBorrowAccessRange (.concrete root)
    (Size.ofBytes offset) (Size.ofBytes 1) .Read
    (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
  have readDone : (physical.entry.allocation.extra.performBorrowAccessRange
      (CandidateCurrentWindowPointerChecks.extraOf physical.pointer.provenance) (Size.ofBytes (UInt64.ofNat physical.offset.toNat))
      (Size.ofBytes 1) .Read (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags
      .VisitChildrenOfAccessed).status=.Completed := by
    rw [allocationEq,pointerEq,offsetEq,UInt64.ofNat_toNat,ready.value]
    exact stages.1
  have parentEq : (physical.entry.allocation.extra.performBorrowAccessRange
      (CandidateCurrentWindowPointerChecks.extraOf physical.pointer.provenance) (Size.ofBytes (UInt64.ofNat physical.offset.toNat))
      (Size.ofBytes 1) .Read (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags
      .VisitChildrenOfAccessed).tree=parent.tree := by
    rw [allocationEq,pointerEq,offsetEq,UInt64.ofNat_toNat,ready.value];rfl
  have childEq : parent.tree.newChild (Size.ofBytes (UInt64.ofNat physical.offset.toNat))
      (CandidateCurrentWindowPointerChecks.extraOf physical.pointer.provenance) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 1) ChildBorrow.fnEntryLocation) MachineHooks.protectionPolicy.outsidePermission
      MachineHooks.protectionPolicy.protector.isSome=⟨output.child.tree,.ok ()⟩ := by
    rw [pointerEq,offsetEq,UInt64.ofNat_toNat,ready.value,childTree]
    exact GeneralBorrowFreshReborrowStages.child_complete _ stages.2
  have virtualRetag:=CurrentCallBoolProtection.retag_of_steps options remaining span ctx options.limits.retag initial tracker
    frames frame borrowFrame ready.enabled frameBorrow place physical.layout physical.pointer physical.physicalPointer
    physical.id physical.offset.toNat selectedBinding physical.entry physical.live fresh ready.race parent.tree output.child.tree
    parentEq readDone childEq
  have entryEq : physical.entry=⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)⟩ := by
    have live:=physical.live
    rw [idEq] at live
    have original : initial.memory.live.find? (fun row=>row.1==family.allocation)=
        some (family.allocation,⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)⟩):=
      MemoryCopyBridge.live_lookup_replaced _ _ _
    exact (Prod.mk.inj (Option.some.inj (live.symm.trans original))).2
  have sameState : retagged options frames frame borrowFrame machine tracker fresh family.allocation root source converted offset=
      ReturnProtection.borrowedState frames frame borrowFrame initial tracker fresh physical.id physical.entry output.child.tree := by
    rw [retagged_seeded,entryEq,idEq,childTree]
  rw [sameState] at actualRetag
  have nextPlaceEq : TypedRetagGeneric.retaggedPlace place family.allocation tracker.global.nextPointerTag=
      TypedRetagGeneric.retaggedPlace place physical.id tracker.global.nextPointerTag := by rw [idEq]
  rw [nextPlaceEq] at actualRetag
  have sameProtect:=protect_same_continuation options remaining span place _
    (Storage.withCurrent frames frame machine) (Storage.withCurrent frames frame initial) _ tracker tracker
    ready.enabled ready.enabled actualRetag virtualRetag
  change TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag options.limits.retag place
    (Storage.withCurrent frames frame initial)=_ at protectActual
  rw [←sameProtect] at protectActual
  let constructor:=ReturnProtection.borrowedState frames frame borrowFrame initial tracker fresh physical.id physical.entry output.child.tree
  let post : RootState:={constructor with machine:={constructor.machine with memory:={constructor.machine.memory with live:=
    ((constructor.machine.memory.live.filter (fun row=>row.1!=physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}}
  have constructorPresent : Present (ActualWorld constructor.machine) physical.id (selected.allocation.setExtra output.child.tree) := by
    simp only [Present,ActualWorld,Array.toList_map]
    apply List.mem_map.mpr
    refine ⟨(physical.id,{physical.entry with allocation:=physical.entry.allocation.setExtra output.child.tree}),?_,?_⟩
    · exact Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inr rfl))
    · rw [selectedAllocation]
  have finalPresent : Present (ActualWorld post.machine) physical.id updated := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(physical.id,{physical.entry with allocation:=updated}),
      Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inr rfl)),rfl⟩
  have rootTag : output.global.rootTag? physical.id=tracker.global.rootTag? physical.id := by rw [global];rfl
  have sizeSelected : updated.byteSize=selected.allocation.byteSize:=sizeEq.trans (congrArg Allocation.byteSize selectedAllocation)
  have lengthSelected : updated.len=selected.allocation.len:=lengthEq.trans (congrArg Allocation.len selectedAllocation)
  have extraSelected : updated.extra=(output.child.tree.performBorrowAccessRange (.concrete output.tag)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed).tree := by
    rw [tag,global];exact extra
  obtain ⟨data,owner,Q,pointerQ,allocationQ,completionQ,currentRuntime,_,leaf,hidden,nodeAtFinal,active,parentIssued,parentBinding⟩:=CurrentCallSelectedBoolWindow.window selected selectedRun borrowFrame fresh
    distinct short physical.offset rfl output child actual witness tag constructor.machine constructorPresent rootTag
    post.machine updated finalPresent lengthSelected sizeSelected extraSelected
  have trackerEq : (⟨output.global,tracker.retagMode⟩ : MachineHooks.BorrowState)=
      registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag := by rw [global];rfl
  let finalQ : UniformWindow post.machine (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag)
      data owner family.allocation offset.toNat 1 .ret := {
    loan:=Q.loan,pointer:=Q.pointer,allocation:=Q.allocation,precise:=Q.precise,
    loanAt:=Q.loanAt,pointerAt:=Q.pointerAt,pointerId:=Q.pointerId.trans idEq,
    present:=by rw [←idEq];exact Q.present,
    preciseAt:=by rw [←idEq];exact Q.preciseAt,
    binding:=Q.binding,issued:=by simpa only [trackerEq,idEq] using Q.issued,
    parents:=Q.parents,
    window:=by
      intro byte hit
      have oldHit : Window physical.id physical.offset.toNat 1 byte := by simpa only [idEq,offsetEq] using hit
      simpa only [global,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,
        GlobalState.addProtector,registeredTracker,registeredGlobal,allocatedTracker,ite_true] using Q.window byte oldHit}
  refine ⟨post,data,owner,finalQ,protectActual,?_,?_,?_,?_,?_,rfl,rfl,?_,?_,?_⟩
  · exact tracked
  · rw [←idEq];rfl
  · change DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra _
    rw [allocationQ]
    rw [global] at currentRuntime
    exact currentRuntime
  · change post.machine.memory.live=_
    change finalQ.allocation=updated at allocationQ
    rw [allocationQ]
    simp only [post,constructor,ReturnProtection.borrowedState,RetagEntry.updatedMemory,
      initial,seeded,GlobalDataOnlyMaterialize.cached,Storage.withCurrent]
    rw [entryEq,idEq]
    simp only [Array.filter_push,beq_self_eq_true,bne_self_eq_false,Bool.false_eq_true,ite_false,Array.filter_filter,Bool.and_self]
  · change finalQ.allocation=updated at allocationQ
    rw [allocationQ]
    simp only [post,constructor,ReturnProtection.borrowedState,RetagEntry.updatedMemory,
      initial,seeded,GlobalDataOnlyMaterialize.cached,Storage.withCurrent,registeredMachine,allocatedMachine,MemoryExtras.putAllocation]
    rw [entryEq,idEq]
    simp only [Array.filter_push,beq_self_eq_true,bne_self_eq_false,Bool.false_eq_true,ite_false,Array.filter_filter,Bool.and_self]
  · change SpatialDelegation post.machine _ family.allocation Q.allocation Q.precise.completion allocationRoot
    rw [allocationQ]
    change SpatialDelegation post.machine ⟨output.global,tracker.retagMode⟩ physical.id updated Q.precise.completion B.pointer.grant at parentIssued
    rw [bPointer] at parentIssued
    simpa only [trackerEq,idEq,Family.at] using parentIssued
  · change PointerBinds Q.allocation (family.at allocationRoot)
    rw [allocationQ]
    change PointerBinds updated B.pointer at parentBinding
    rw [bPointer] at parentBinding
    exact parentBinding
  · let mutationInput:=(physical.entry.allocation.setExtra output.child.tree).setExtra
        (output.child.tree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag)
          (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write
          (registeredGlobal (allocatedTracker tracker fresh) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree
    obtain ⟨other,otherWrite,_,_,_,_,_,maskValid,maskLen,clear⟩:=S02SameDestinationUninitInitializedMutation.uninit
      mutationInput physical.capacity physical.offset physical.bytes physical.size physical.mutable
      physical.maskValid physical.maskLength physical.provenanceMap physical.bounds
    have equal : other=updated := by injection (otherWrite.symm.trans write)
    subst other
    have endpoint:=(DuplicatePrefix.source_end (Size.ofBytes physical.offset) 1 (by
      have bound:=physical.bounds
      have room:=physical.capacity.toNat_lt
      simpa [Size.ofBytes] using (show physical.offset.toNat+1<2^64 by omega)))
    have pointerBounds:=S03UninitProvenance.clear_pointer_bounds mutationInput.provenanceMap updated.provenanceMap
      (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes (physical.offset+1))
      (AllocationCopy.snapshot mutationInput) mutationInput.len endpoint
      (ProvenanceCopy.WellFormed.pointerBounds physical.provenanceMap) clear
    let P : CurrentCallBoolScalarWrite.Window post.machine place := {
      pointer:=physical.pointer,physicalPointer:=physical.physicalPointer,layout:=physical.layout,aligned:=physical.aligned,
      id:=physical.id,entry:={physical.entry with allocation:=updated},base:=physical.base,offset:=physical.offset,capacity:=physical.capacity,
      live:=MemoryCopyBridge.live_lookup_replaced _ _ _,cachedBase:=physical.cachedBase,pointerAddress:=physical.pointerAddress,
      bounds:=physical.bounds,size:=sizeEq.trans physical.size,bytes:=lengthEq.trans physical.bytes,mutable:=mutable,
      maskValid:=maskValid,maskLength:=maskLen.trans physical.maskLength,
      pointerBounds:=by rw [lengthEq];exact pointerBounds}
    have windowBounds : physical.offset.toNat+1≤selected.allocation.extra.locations.size.bytes.toNat := by
      rw [selected.issued.capability.treeExtent,←selected.issued.capability.extent]
      have available:=(selected.window (physical.id,physical.offset.toNat) ⟨rfl,by omega,by omega⟩).1
      omega
    have finalDistinct : updated.extra.roots.toList.Nodup := by
      have bounds : physical.offset.toNat+1≤selected.allocation.extra.locations.size.bytes.toNat := by
        rw [selected.issued.capability.treeExtent,←selected.issued.capability.extent]
        have available:=(selected.window (physical.id,physical.offset.toNat) ⟨rfl,by omega,by omega⟩).1
        omega
      have rootAfter:=(positive_global_rule ".CurrentCallSelectedBoolProtection.roots") selected selectedRun borrowFrame fresh
        rfl distinct (by omega) (by omega) physical.offset 1 rfl rfl (by decide) bounds output actual
      obtain ⟨_,_,_,_,_,rootFrame,_,_⟩:=CurrentCallSelectedBoolCurrent.operation_runtime selected selectedRun borrowFrame fresh
        distinct short physical.offset rfl output child actual witness tag constructor.machine constructorPresent rootTag .VisitChildrenOfAccessed
      rw [extraSelected,rootFrame]
      exact rootAfter
    have finalNodes : updated.extra.nodes.size≤2 := by
      have bound:=(positive_global_rule ".CurrentCallSelectedBoolProtection.growth") selected selectedRun borrowFrame fresh rfl distinct
        (by omega) (by omega) physical.offset 1 rfl rfl (by decide) windowBounds output actual
      obtain ⟨_,_,_,_,nodes,_,_,_⟩:=CurrentCallSelectedBoolCurrent.operation_runtime selected selectedRun borrowFrame fresh
        distinct short physical.offset rfl output child actual witness tag constructor.machine constructorPresent rootTag .VisitChildrenOfAccessed
      have initialNodes : selected.allocation.extra.nodes.size=1 := by change B.allocation.extra.nodes.size=1;rw [bAllocation];rfl
      rw [extraSelected,nodes]
      rw [initialNodes] at bound
      exact bound
    have finalShort : updated.extra.nodes.size<65536:=Nat.lt_of_le_of_lt finalNodes (by decide)
    have originalIssued : SpatialDelegation post.machine (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag)
        physical.id Q.allocation Q.precise.completion B.pointer.grant := by
      rw [allocationQ]
      simpa only [trackerEq] using parentIssued
    have finalBinding : CandidateCallBindings.WindowBinding post.machine P.pointer physical.id physical.offset.toNat 1 := by
      obtain ⟨old,address,oldLive,cachedAddress,storage,addressRoom,bounds,pointerAddress,nonnull,provenance⟩:=selectedBinding
      have oldEq : old=physical.entry := (Prod.mk.inj (Option.some.inj (oldLive.symm.trans physical.live))).2
      subst old
      refine ⟨{physical.entry with allocation:=updated},address,P.live,cachedAddress,?_,?_,?_,pointerAddress,nonnull,?_⟩
      · change updated.len=updated.byteSize.bytes.toNat
        rw [lengthEq,sizeEq];exact storage
      · rw [lengthEq];exact addressRoom
      · rw [lengthEq];exact bounds
      · change (match physical.pointer.provenance with
          | .concrete supplied tag=>supplied=physical.id
          | .wildcard=>_)
        rw [pointerEq,ready.value]
        change family.allocation=physical.id
        exact idEq.symm
    have edge : Q.precise.completion.parents[Q.pointer.grant.toNat]?=some (some B.pointer.grant) := by
      rw [pointerQ,completionQ]
      exact witness.edge
    have currentNode : Q.allocation.extra.nodes.get Q.pointer.grant=some witness.node := by
      rw [allocationQ,pointerQ];exact nodeAtFinal
    let Rwindow : UniformWindow post.machine (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag)
        data owner physical.id physical.offset.toNat 1 .ret := {
      loan:=Q.loan,pointer:=Q.pointer,allocation:=Q.allocation,precise:=Q.precise,
      loanAt:=Q.loanAt,pointerAt:=Q.pointerAt,pointerId:=Q.pointerId,present:=Q.present,preciseAt:=Q.preciseAt,
      binding:=Q.binding,issued:=by simpa only [trackerEq] using Q.issued,parents:=Q.parents,
      window:=by
        intro byte hit
        simpa only [global,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,
          GlobalState.addProtector,registeredTracker,registeredGlobal,allocatedTracker,ite_true] using Q.window byte hit}
    let R : CurrentCallPostEntryCheckpoint.Return post.machine
        (registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag) place := {
      data:=data,owner:=owner,id:=physical.id,offset:=physical.offset.toNat,
      window:=Rwindow,
      physical:=P,physicalId:=rfl,physicalOffset:=rfl,physicalAllocation:=allocationQ.symm,
      binding:=finalBinding,original:=B.pointer,originalId:=B.pointerId.trans idEq.symm,
      originalPointer:=samePointer.symm,originalIssued:=originalIssued,
      originalBinding:=by rw [allocationQ];exact parentBinding,edge:=edge,
      runtime:=by rw [allocationQ];rw [global] at currentRuntime;exact currentRuntime,
      distinct:=by rw [allocationQ];exact finalDistinct,short:=by rw [allocationQ];exact finalShort,
      node:=witness.node,nodeAt:=currentNode,leaf:=leaf,hidden:=hidden,
      activity:=by
        change GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra Q.pointer.grant .Write physical.offset (physical.offset+1)
        rw [allocationQ,pointerQ];exact active,
      profile:=windowReady}
    refine ⟨R,idEq,congrArg UInt64.toNat offsetEq,bPointer,witness.tag.trans tag,rfl,?_⟩
    change Q.allocation.extra.nodes.size≤2
    rw [allocationQ]
    exact finalNodes

end
end DuplicatePrefix.CurrentCallLazyBoolTyped
