import duplicate_prefix.CurrentCallLazyCurrentDescriptor
import duplicate_prefix.CurrentCallFamilySatisfaction
import duplicate_prefix.CurrentCallSupportChain
import duplicate_prefix.CurrentCallSupportChainExtraction
import duplicate_prefix.CandidateCurrentBoolUninitWrite
import duplicate_prefix.GeneralBorrowParentTagRootFrames

/-! A bounded latent-Bool adapter: CURRENT data-only mutable memory with a
cached selected root/address. The original ensure runs once before any Bool
retag. Uninitialized bytes are allowed. This is not descriptor/cache coverage
for all ordinary inputs, and no Bool allocation is assumed initially live. -/
namespace DuplicatePrefix.CurrentCallLazyBoolEnsure
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization CurrentCallSpatialCover CurrentCallFamilySatisfaction
open CanonicalConfigFacts GeneralBorrowFullSharedSeed GeneralRangeMapOrigins
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Independent CURRENT physical/cache data, not a successful materialization
or an initial live Bool window. No initialization-value bit is required. -/
structure Ready (options : EvalConfigurationCore.Options) (before : RootState)
    (tracker : MachineHooks.BorrowState) (family : Family) (root : BorTag)
    (source : Allocation CtfeProvenance Unit) (base offset : UInt64) (place : MPlaceTy Provenance) : Prop where
  descriptor : before.machine.memory.findGlobal? family.allocation=some
    ⟨family.allocation,.memory,source.byteSize,source.align,source.mutability,some (.memory source)⟩
  emptyProvenance : source.provenanceMap=ProvenanceMap.new
  enabled : before.machine.borrowTracker=some tracker
  rootCached : tracker.global.rootTag? family.allocation=some root
  race : before.machine.dataRace=none
  noExtras : (before.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row=>row.1==family.allocation))=false
  absent : before.machine.memory.live.find? (fun row=>row.1==family.allocation)=none
  cached : before.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==family.allocation)=some ⟨family.allocation,base⟩
  storage : source.len=source.byteSize.bytes.toNat
  maskValid : InitMaskCopy.WellFormed source.initializationMask
  maskLength : source.initializationMask.len=source.byteSize
  mutable : source.mutability=.Mut
  bounds : offset.toNat+1≤source.byteSize.bytes.toNat
  addressRoom : base.toNat+source.len<2^64
  nonnull : base+offset≠0
  value : family.value=Pointer.new (.concrete family.allocation root) (Size.ofBytes (base+offset))
  physicalPointer : place.mplace.ptr=family.value.withOptionalProvenance
  layout : place.layout=RootCompilerFacts.boolLayout
  aligned : place.mplace.misaligned=none
  rootBelow : root.value.toNat<tracker.global.nextPointerTag.value.toNat
  protectors : ∀row∈tracker.global.protectedTags.entries,row.1.value.toNat<tracker.global.nextPointerTag.value.toNat

/-- Retain the real data-only conversion's provenance facts as well as its
attributes; generic relocation attributes alone do not certify Bool storage. -/
private theorem materialize (options : EvalConfigurationCore.Options) (choice : Unit) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (before : RootState) (tracker : MachineHooks.BorrowState)
    (family : Family) (root : BorTag) (source : Allocation CtfeProvenance Unit) (base offset : UInt64)
    (place : MPlaceTy Provenance) (ready : Ready options before tracker family root source base offset place) :
    ∃converted : Allocation Provenance Unit,GlobalDataOnlyConversion.Facts source converted ∧
      (PreparedContracts.actualConfig options choice remaining span).retag.ensureTreeExtra family.allocation before=
        .ok () {before with machine:=(GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options)
          before.machine family.allocation .global (converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)))} := by
  let compiler:=PreparedReflection.actual.compiler
  let image:=PreparedReflection.actual.image
  let extras:=GlobalDataOnlyActualConfig.extras options
  let leaves:=(Machine.leaves PreparedReflection.actual.prepared options.place.debugAssertions).pointerSource
  let pointers:=EvalPointerSource.make compiler image extras leaves choice
  let address:=EvalPointerSource.address compiler image leaves choice
  obtain ⟨converted,facts,adjust⟩:=GlobalDataOnlyActualBytes.adjust_exists compiler image extras leaves address pointers.rootPointer
    before.machine tracker family.allocation root source (by rfl) ready.emptyProvenance ready.enabled ready.rootCached ready.race ready.noExtras
  let allocation:=converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)
  let after:=GlobalDataOnlyMaterialize.cached extras before.machine family.allocation .global allocation
  have raw : MemoryLifecycle.getAllocRaw before.machine.memory ⟨before.machine,none⟩ family.allocation (some .global) pointers.globals=
      ⟨after.memory,⟨after,none⟩,.ok allocation⟩ := by
    simp only [MemoryLifecycle.getAllocRaw,ready.absent,MemoryLifecycle.getGlobalAlloc,ready.descriptor,
      pointers,EvalPointerSource.make,EvalGlobalAllocationMachine.make,GlobalAllocationMachine.hooks,Id.run,bind,Bind.bind,pure,Pure.pure]
    unfold_global_data ".Miri.Interpreter.GlobalAllocationMachine.bridge"
    simp only [GlobalDataOnlyActualBytes.leaves,pointers,address,EvalPointerSource.make,pure,Pure.pure] at adjust
    simp only [adjust]
    unfold_global_data ".Miri.Memory.MemoryState.insertLive"
    rfl
  refine ⟨converted,facts,?_⟩
  rw [GlobalDataOnlyActualConfig.actual_ensure]
  change pointers.pointers.ensureTreeExtra family.allocation before=.ok () {before with machine:=after}
  simp only [pointers,EvalPointerSource.make,pure,Pure.pure] at raw
  simp only [pointers,EvalPointerSource.make,PointerSource.pointers,GlobalAllocationMachine.ensure,get,getThe,
    MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    pure,Pure.pure,EStateM.pure,raw]

private def rootChain (root : BorTag) (size : Size) : CurrentCallSupportChain.Chain (BorrowTree.new root size) allocationRoot :=
  .root (.refl allocationRoot _ (BorrowTree.new_root_node root size))

def completion (root : BorTag) (size : Size) : Completion := (rootChain root size).completion

private theorem seed_embeds (allocation : Allocation Provenance BorrowTree) (capacity : UInt64)
    (root : BorTag) (nonzero : capacity≠0) (shape : allocation.extra=BorrowTree.new root (Size.ofBytes capacity))
    (held : ProtectedTags) (C : Completion) (byte : Nat) : Embeds allocation held C allocationRoot byte .exclusive := by
  have model:=tree_eq capacity nonzero root
  change BorrowTree.new root (Size.ofBytes capacity)=_ at model
  intro segment member lower upper index node nodeAt
  rw [shape,model] at member nodeAt
  have segmentEq : segment=⟨⟨0,capacity⟩,GeneralBorrowFullSharedSeed.location⟩:=by
    simpa only [RangeMapNonempty.homogeneous,List.mem_singleton] using member
  subst segment
  have bounded:=GeneralBorrowNodeUpdate.lookup_valid (⟨#[some (GeneralBorrowFullSharedSeed.node root)]⟩ : UniValMap TreeNode) index node nodeAt
  have same : index=allocationRoot:=GeneralBorrowNodeUpdate.index_injective index allocationRoot
    (by change index.toNat=0;change index.toNat<1 at bounded;omega)
  subst index
  have sameNode : node=GeneralBorrowFullSharedSeed.node root := (Option.some.inj nodeAt).symm
  subst node
  refine ⟨?_,fun _=>Below.refl allocationRoot⟩
  intro _
  change .exclusive∈tokens (denote GeneralBorrowWildcardLeaf.unique (held.contains root))
  simp [tokens,denote,GeneralBorrowWildcardLeaf.unique]

/-- Technical window indices retain the fixed family value. They assert no
new actual copy or whole current-denotation interpretation. -/
def identities (family : Family) (C : Completion) : Identities :=
  ⟨⟨#[(family.allocation,⟨C,#[]⟩)],#[family.at allocationRoot],#[⟨0,none,0⟩],fun _ _=>none⟩,
    #[⟨0,family.value⟩],#[]⟩

/-- The actual inner ensure starts on the ORIGINAL state. Its post-world has
an uninitialized-permitted physical Bool window and current root authority. -/
theorem ensure (options : EvalConfigurationCore.Options) (choice : Unit) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (before : RootState) (tracker : MachineHooks.BorrowState)
    (family : Family) (root : BorTag) (source : Allocation CtfeProvenance Unit) (base offset : UInt64)
    (place : MPlaceTy Provenance) (ready : Ready options before tracker family root source base offset place) :
    ∃converted : Allocation Provenance Unit,GlobalDataOnlyConversion.Facts source converted ∧
    let allocation:=converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)
    let after:=GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options) before.machine family.allocation .global allocation
    (PreparedContracts.actualConfig options choice remaining span).retag.ensureTreeExtra family.allocation before=.ok () {before with machine:=after} ∧
    after.borrowTracker=before.machine.borrowTracker ∧after.user.addresses=before.machine.user.addresses ∧
    AllocationCapability after tracker family.allocation allocation ∧
    DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global ∧
    CandidateCallBindings.WindowBinding after family.value family.allocation offset.toNat 1 ∧
    Satisfies tracker family allocation (Window family.allocation offset.toNat 1) ∧
    ∃physical : CandidateCurrentBoolUninitWrite.PhysicalWindow after place,
      physical.id=family.allocation ∧physical.pointer=family.value ∧physical.entry.allocation=allocation ∧physical.offset=offset ∧
    ∃B : UniformWindow after tracker (identities family (completion root source.byteSize)) 0 family.allocation offset.toNat 1 .ret,
      B.pointer=family.at allocationRoot ∧B.allocation=allocation := by
  obtain ⟨converted,facts,actual⟩:=materialize options choice remaining span before tracker family root source base offset place ready
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
    exact (rootChain root source.byteSize).parents runtime.formed.toGraphState
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
      refine ⟨?_,seed_embeds allocation source.byteSize.bytes root nonzero rfl tracker.global.protectedTags _ byte.2⟩
      change byte.2<converted.len
      rw [facts.storage,ready.storage]
      have bound:=ready.bounds
      have upper:=hit.2.2
      omega}
  have owned : Satisfies tracker family allocation (Window family.allocation offset.toNat 1):=by
    intro byte hit
    obtain ⟨chain,_,support⟩:=CurrentCallSupportChainExtraction.extract_support B.parents B.issued (B.window byte hit).2
    exact ⟨hit.1,allocationRoot,chain,pointerBind,support⟩
  exact ⟨converted,facts,actual,rfl,rfl,cap,runtime,binding,owned,physical,rfl,rfl,rfl,rfl,B,rfl,rfl⟩

private theorem filter_absent {K U : Type} (before : MachineHooks.MachineState K U) (id : AllocId)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none) :
    before.memory.live.filter (fun row=>row.1!=id)=before.memory.live := by
  apply Array.filter_eq_self.mpr
  intro row member
  simpa using Array.find?_eq_none.mp absent row member

/-- Framing is on the EXACT cached post-machine used by ensure. The existing
live source keeps its allocation, family, physical binding and current rights.
Only the Bool descriptor was latent; the different ID is derived, not assumed.
The SAME fragments are composed, with no new independent content ownership. -/
theorem frame_source (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState) (id : AllocId) (allocation : Allocation Provenance BorrowTree)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (sourceFamily : Family) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceOffset sourceLength : Nat)
    (sourceLive : before.memory.live.find? (fun row=>row.1==sourceFamily.allocation)=some (sourceFamily.allocation,entry))
    (sourceCap : AllocationCapability before tracker sourceFamily.allocation entry.allocation)
    (sourcePhysical : CandidateCallBindings.WindowBinding before sourceFamily.value sourceFamily.allocation sourceOffset sourceLength)
    (sourceOwned : Satisfies tracker sourceFamily entry.allocation (Window sourceFamily.allocation sourceOffset sourceLength))
    (Fs Fr : CandidateFreezeContentResources.Fragment)
    (composable : CandidateFreezeContentResources.Composable Fs Fr) :
    let after:=GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options) before id .global allocation
    id≠sourceFamily.allocation ∧
    after.memory.live.find? (fun row=>row.1==sourceFamily.allocation)=some (sourceFamily.allocation,entry) ∧
    AllocationCapability after tracker sourceFamily.allocation entry.allocation ∧
    CandidateCallBindings.WindowBinding after sourceFamily.value sourceFamily.allocation sourceOffset sourceLength ∧
    Satisfies tracker sourceFamily entry.allocation (Window sourceFamily.allocation sourceOffset sourceLength) ∧
    CandidateFreezeContentResources.Valid (CandidateFreezeContentResources.union Fs Fr) := by
  let after:=GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options) before id .global allocation
  have different : id≠sourceFamily.allocation:=by
    intro same
    have absent':=absent
    rw [same,sourceLive] at absent'
    cases absent'
  have oldLive : ∀ (other : AllocId) (old : LocalAllocation Provenance BorrowTree MiriMemoryKind),
      before.memory.live.find? (fun row=>row.1==other)=some (other,old)→
      after.memory.live.find? (fun row=>row.1==other)=some (other,old):=by
    intro other old found
    simp only [after,GlobalDataOnlyMaterialize.cached,filter_absent before id absent,Array.find?_push,found]
    rfl
  have sourceAfter:=oldLive _ _ sourceLive
  have presentAfter : Present (ActualWorld after) sourceFamily.allocation entry.allocation:=by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(sourceFamily.allocation,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some sourceAfter),rfl⟩
  have capAfter : AllocationCapability after tracker sourceFamily.allocation entry.allocation:=
    ⟨presentAfter,sourceCap.extent,sourceCap.treeExtent,sourceCap.rootSlot,sourceCap.rootNode⟩
  have physicalAfter : CandidateCallBindings.WindowBinding after sourceFamily.value sourceFamily.allocation sourceOffset sourceLength:=by
    obtain ⟨old,base,found,cached,extent,room,bounds,address,nonnull,binding⟩:=sourcePhysical
    exact ⟨old,base,oldLive _ _ found,cached,extent,room,bounds,address,nonnull,binding⟩
  exact ⟨different,sourceAfter,capAfter,physicalAfter,sourceOwned,CandidateFreezeContentResources.union_valid Fs Fr composable⟩

/-- Couple the ONE real ensure with the two fixed content fragments. The Bool
fragment is licensed over the latent descriptor's byte; the already-live source
family and allocation are retained on that same actual post-state. -/
theorem ensure_with_source (options : EvalConfigurationCore.Options) (choice : Unit) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (before : RootState) (tracker : MachineHooks.BorrowState)
    (family : Family) (root : BorTag) (source : Allocation CtfeProvenance Unit) (base offset : UInt64)
    (place : MPlaceTy Provenance) (ready : Ready options before tracker family root source base offset place)
    (sourceFamily : Family) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceOffset sourceLength : Nat)
    (sourceLive : before.machine.memory.live.find? (fun row=>row.1==sourceFamily.allocation)=some (sourceFamily.allocation,entry))
    (sourceCap : AllocationCapability before.machine tracker sourceFamily.allocation entry.allocation)
    (sourcePhysical : CandidateCallBindings.WindowBinding before.machine sourceFamily.value sourceFamily.allocation sourceOffset sourceLength)
    (sourceOwned : Satisfies tracker sourceFamily entry.allocation (Window sourceFamily.allocation sourceOffset sourceLength))
    (Fs Fr : CandidateFreezeContentResources.Fragment) (sourceOwner returnOwner : Nat)
    (sourceCharge : CurrentCallPointwiseSpatialCover.ExactCharge Fs sourceOwner .mut sourceFamily.allocation sourceOffset sourceLength)
    (returnCharge : CurrentCallPointwiseSpatialCover.ExactCharge Fr returnOwner .ret family.allocation offset.toNat 1)
    (composable : CandidateFreezeContentResources.Composable Fs Fr) :
    ∃converted : Allocation Provenance Unit,GlobalDataOnlyConversion.Facts source converted ∧
    let allocation:=converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)
    let after:=GlobalDataOnlyMaterialize.cached (GlobalDataOnlyActualConfig.extras options) before.machine family.allocation .global allocation
    (PreparedContracts.actualConfig options choice remaining span).retag.ensureTreeExtra family.allocation before=.ok () {before with machine:=after} ∧
    AllocationCapability after tracker family.allocation allocation ∧
    DuplicatePrefixBorrowContract.RuntimeFacts allocation.extra tracker.global ∧
    CandidateCallBindings.WindowBinding after family.value family.allocation offset.toNat 1 ∧
    Satisfies tracker family allocation (Window family.allocation offset.toNat 1) ∧
    family.allocation≠sourceFamily.allocation ∧
    after.memory.live.find? (fun row=>row.1==sourceFamily.allocation)=some (sourceFamily.allocation,entry) ∧
    AllocationCapability after tracker sourceFamily.allocation entry.allocation ∧
    CandidateCallBindings.WindowBinding after sourceFamily.value sourceFamily.allocation sourceOffset sourceLength ∧
    Satisfies tracker sourceFamily entry.allocation (Window sourceFamily.allocation sourceOffset sourceLength) ∧
    Satisfies tracker sourceFamily entry.allocation (fun byte=>Fs byte sourceOwner=some ⟨.mut,.active⟩) ∧
    Satisfies tracker family allocation (fun byte=>Fr byte returnOwner=some ⟨.ret,.active⟩) ∧
    CandidateFreezeContentResources.Valid (CandidateFreezeContentResources.union Fs Fr) ∧
    ∃physical : CandidateCurrentBoolUninitWrite.PhysicalWindow after place,
      physical.id=family.allocation ∧physical.pointer=family.value ∧physical.entry.allocation=allocation ∧physical.offset=offset ∧
    ∃B : UniformWindow after tracker (identities family (completion root source.byteSize)) 0 family.allocation offset.toNat 1 .ret,
      B.pointer=family.at allocationRoot ∧B.allocation=allocation := by
  obtain ⟨converted,facts,actual,_,_,cap,runtime,binding,boolOwned,physical,physicalId,physicalPointer,physicalAllocation,physicalOffset,B,BPointer,BAllocation⟩:=
    ensure options choice remaining span before tracker family root source base offset place ready
  let allocation:=converted.mapExtra (fun _=>BorrowTree.new root source.byteSize)
  obtain ⟨different,sourceAfter,capAfter,physicalAfter,ownedAfter,valid⟩:=frame_source options before.machine tracker family.allocation allocation
    ready.absent sourceFamily entry sourceOffset sourceLength sourceLive sourceCap sourcePhysical sourceOwned Fs Fr composable
  have sourceFragment : Satisfies tracker sourceFamily entry.allocation (fun byte=>Fs byte sourceOwner=some ⟨.mut,.active⟩):=
    CurrentCallFamilySatisfaction.restrict ownedAfter (fun byte hit=>(sourceCharge byte).mp hit)
  have returnFragment : Satisfies tracker family allocation (fun byte=>Fr byte returnOwner=some ⟨.ret,.active⟩):=
    CurrentCallFamilySatisfaction.restrict boolOwned (fun byte hit=>(returnCharge byte).mp hit)
  exact ⟨converted,facts,actual,cap,runtime,binding,boolOwned,different,sourceAfter,capAfter,physicalAfter,ownedAfter,
    sourceFragment,returnFragment,valid,physical,physicalId,physicalPointer,physicalAllocation,physicalOffset,B,BPointer,BAllocation⟩

end
end DuplicatePrefix.CurrentCallLazyBoolEnsure
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallLazyBoolEnsure" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved lazy Bool ensure dependency {dependency}"
