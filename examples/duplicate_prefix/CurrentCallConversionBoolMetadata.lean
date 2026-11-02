import duplicate_prefix.CurrentCallConversionBoolModel

/-! Allocation metadata of the SAME actual Bool retag and primitive uninit
write. No physical-span inference substitutes for the real mutation. -/
namespace DuplicatePrefix.CurrentCallConversionBoolMetadata
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata TypedBorrowSteps
open GeneralBorrowFullSharedSeed CurrentCallLazyBoolEnsure CurrentCallFamilySatisfaction
open ReferenceBorrowDriver CurrentCallOrdinaryInput CurrentCallConversionSourceCopy CurrentCallConversionBoolPhase CurrentCallConversionBool
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
noncomputable section

open Lean Elab Tactic in
elab "bool_metadata_rule " suffix:str : term => do
  let found:=(←getEnv).constants.toList.filter (fun (name,_)=>name.toString.endsWith suffix.getString)
  match found with | [(name,_)]=>return mkConst name | _=>throwError "expected unique checked Bool rule {suffix.getString}"

variable {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
variable {machine : Before} {tracker : MachineHooks.BorrowState}
variable {frames : Array CompilerFrameContext.ActualFrame} {frame : CompilerFrameContext.ActualFrame}
variable {borrowFrame : FrameState} {place : MPlaceTy Provenance}
variable {D : CurrentData machine tracker frames frame borrowFrame place}
variable {externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance)}
variable {tail : List AllocId} {charge reserve : Nat} {finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState}
variable {finalTape : ExecutionChoices.Tape}
variable {result : CurrentCallConversionFiniteFold.Result D.source PreparedReflection.actual.compiler.runtime.target.base
  (CurrentCallConversionActualEnsure.hooks options).address externStatic D.registered.machine D.next
  tail charge reserve finalAddresses finalTape}

theorem mutation (ctx : ActualRetagContext.Context options remaining span)
    (wiring : (CurrentCallConversionActualEnsure.hooks options).rootPointer=
      PointerSource.globalRootPointer EvalPointerSource.tape (CurrentCallConversionActualEnsure.hooks options).address externStatic)
    (O : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result) :
    ∃tree,Allocation.writeUninit (allocRange (Size.ofBytes D.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
      (result.converted.mapExtra (fun _=>tree))=.ok () O.output.window.allocation := by
  let afterTracker : MachineHooks.BorrowState:={D.next with global:=result.global}
  have conversion : Allocation.adjustFromTcx D.source PreparedReflection.actual.compiler.runtime.target.base
      (fun _ _ state=>.ok (AllocationCopy.snapshot D.source) state)
      (CurrentCallConversionActualEnsure.hooks options).rootPointer D.registered.machine=.ok result.converted result.machine := by
    rw [wiring];exact result.completed
  have afterEnabled : result.machine.borrowTracker=some afterTracker := by rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
  have afterRoot : afterTracker.global.rootTag? D.family.allocation=some D.root:=result.roots _ _ D.rootCached
  have afterCached : result.machine.user.addresses.baseAddr.find? (fun row=>row.allocId==D.family.allocation)=some ⟨D.family.allocation,D.base⟩ := by
    rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact result.bases _ _ D.cached
  have afterRace : result.machine.dataRace=none := by rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact D.race
  have afterGhost : result.machine.user.payload.ghost=false := by rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact D.ghost
  have afterBackend : result.machine.user.payload.payload.user.backend=.none := by rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact D.backend
  have afterExtras : result.machine.user.payload.payload.user.runtime.extras.allocations.any (fun row=>row.1==D.family.allocation)=false := by
    rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact D.registry
  have bounds : D.offset.toNat + 1 ≤ D.source.byteSize.bytes.toNat := by
    simpa only [UInt64.toNat_one] using D.physical.2.2.1
  have ptr : place.mplace.ptr = Pointer.new (some (.concrete D.family.allocation D.root)) (Size.ofBytes (D.base + D.offset)) := by
    rw [D.physicalPointer, D.value]; rfl
  have actualRetag := retag options remaining span ctx frames frame borrowFrame D.frameBorrow machine tracker D.enabled D.fresh
    D.family.allocation D.root D.source D.base D.offset place ptr D.layout D.current D.absent D.noFunction D.noVaList D.cached bounds D.rootBelow D.protectors
    result.converted result.attributes result.machine afterTracker conversion afterEnabled afterRoot afterRace afterExtras result.flags
  let view := {rootMachine options result.machine D.family.allocation D.root result.converted with borrowTracker := some tracker}
  have live : view.memory.live.find? (fun row => row.1 == D.family.allocation) =
      some (D.family.allocation, ⟨.machine .global, result.converted.mapExtra (fun _ => BorrowTree.new D.root D.source.byteSize)⟩) := by
    rw [← result.attributes.size]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  obtain ⟨_, _, _, _, P, idEq, pointerEq, allocationEq, offsetEq, W, wPointer, wAllocation⟩ :=
    root_view view tracker D.family D.root D.source result.converted result.attributes result.wellFormed D.base D.offset place D.value D.physicalPointer D.layout D.aligned
      D.physical live afterCached D.rootCached D.addressRoom D.nonnull D.rootBelow D.protectors
  have samePointer : P.pointer = W.pointer.value := by rw [pointerEq, wPointer]; rfl
  have sameAllocation : P.entry.allocation = W.allocation := allocationEq.trans wAllocation.symm
  have run : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global := by
    rw [wAllocation]
    exact (root_view view tracker D.family D.root D.source result.converted result.attributes result.wellFormed D.base D.offset place D.value D.physicalPointer D.layout D.aligned
      D.physical live afterCached D.rootCached D.addressRoom D.nonnull D.rootBelow D.protectors).2.1
  have bind : CandidateCallBindings.WindowBinding view P.pointer P.id P.offset.toNat 1 := by
    rw [pointerEq, idEq, offsetEq]
    exact (root_view view tracker D.family D.root D.source result.converted result.attributes result.wellFormed D.base D.offset place D.value D.physicalPointer D.layout D.aligned
      D.physical live afterCached D.rootCached D.addressRoom D.nonnull D.rootBelow D.protectors).2.2.1
  have distinct : W.allocation.extra.roots.toList.Nodup := by rw [wAllocation]; change ([allocationRoot] : List UniIndex).Nodup; simp
  have short : W.allocation.extra.nodes.size + 1 < 65536 := by rw [wAllocation]; change 2 < 65536; decide
  have treeBounds : P.offset.toNat + 1 ≤ W.allocation.extra.locations.size.bytes.toNat := by
    rw [wAllocation, offsetEq]
    have nonzero : D.source.byteSize.bytes ≠ 0 := by
      intro zero
      rw [zero] at bounds
      simp only [UInt64.toNat_zero] at bounds
      omega
    change D.offset.toNat + 1 ≤ (BorrowTree.new D.root (Size.ofBytes D.source.byteSize.bytes)).locations.size.bytes.toNat
    have shape := tree_eq D.source.byteSize.bytes nonzero D.root
    change BorrowTree.new D.root (Size.ofBytes D.source.byteSize.bytes) = _ at shape
    rw [shape]
    exact bounds
  obtain ⟨output, child, actual, tag, globalEq, _, _, _, _, ⟨witness⟩⟩ :=
    CurrentCallResourceFnEntry.correlated_borrow_selected W run borrowFrame D.fresh rfl distinct (by omega) (by omega)
      P.offset 1 rfl rfl (by decide) treeBounds
  have literalEq : output = CurrentCallTypedFnEntry.literal W.allocation.extra tracker.global borrowFrame P.id D.fresh
      W.pointer.value.provenance P.offset 1 :=
    Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ D.fresh _ _ _))
  have childTree : output.child.tree = PositiveGlobalTypedReborrow.finalTree D.root tracker.global.nextPointerTag result.converted.byteSize
      afterTracker.global.protectedTags D.offset 1 := by
    rw [literalEq, wAllocation, wPointer, offsetEq]
    change (CurrentCallTypedFnEntry.literal (BorrowTree.new D.root D.source.byteSize) tracker.global borrowFrame P.id D.fresh
      D.family.value.provenance D.offset 1).child.tree = _
    rw [D.value, result.attributes.size, result.flags]
    rfl
  have entryEq : P.entry = ⟨.machine .global, result.converted.mapExtra (fun _ => BorrowTree.new D.root D.source.byteSize)⟩ := by
    have pLive := P.live
    rw [idEq, live] at pLive
    exact (Prod.mk.inj (Option.some.inj pLive)).2.symm
  let constructor := Storage.withCurrent frames (registeredFrame frame borrowFrame D.family.allocation tracker.global.nextPointerTag)
    (childMachine options result.machine D.family.allocation D.root tracker.global.nextPointerTag result.converted afterTracker.global.protectedTags D.offset 1)
  have ctorLive : constructor.machine.memory.live.find? (fun row => row.1 == P.id) =
      some (P.id, {P.entry with allocation := P.entry.allocation.setExtra output.child.tree}) := by
    rw [idEq, entryEq, childTree]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  obtain ⟨physical,idPhysical,offsetPhysical,entryPhysical,concretePhysical⟩:=
    (bool_metadata_rule ".CurrentCallConversionBool.constructor_physical") P constructor.machine output.child.tree output.tag ctorLive (by rfl)
  have present : Present (ActualWorld constructor.machine) P.id (W.allocation.setExtra output.child.tree) := by
    have live:=physical.live
    rw [idPhysical,entryPhysical,sameAllocation] at live
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨_,Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
  have rootTag : output.global.rootTag? P.id=tracker.global.rootTag? P.id := by rw [globalEq];rfl
  have done:=(CurrentCallSelectedBoolCurrent.operation_runtime W run borrowFrame D.fresh distinct short
    P.offset rfl output child actual witness tag constructor.machine present rootTag .VisitChildrenOfAccessed).1
  have flagsOutput : afterTracker.global.protectedTags=output.global.protectedTags := by rw [globalEq];exact result.flags
  have completed : (physical.entry.allocation.extra.performBorrowAccessRange (.concrete output.tag)
      (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write afterTracker.global.protectedTags .VisitChildrenOfAccessed).status=.Completed := by
    rw [entryPhysical,offsetPhysical,flagsOutput];exact done
  have selectedExtras : constructor.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==physical.id)=
      some (physical.id,⟨none,#[]⟩) := by
    rw [idPhysical,idEq]
    change (((result.machine.user.payload.payload.user.runtime.extras.allocations.filter (fun row=>row.1!=D.family.allocation)).push
      (D.family.allocation,⟨none,#[]⟩)).find? (fun row=>row.1==D.family.allocation))=_
    have noMatch : (fun row : AllocId×MemoryExtras.AllocationExtra Unit=>
      decide ((row.1!=D.family.allocation)=true ∧(row.1==D.family.allocation)=true))=(fun _=>false) := by
      funext row;by_cases equal : row.1=D.family.allocation <;> simp [equal]
    have emptyFind : result.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun _=>false)=none := by simp [Array.find?_eq_none]
    simp [Array.find?_push,Array.find?_filter,noMatch,emptyFind]
  have tracked : constructor.machine.borrowTracker=some afterTracker := afterEnabled
  have ghost : constructor.machine.user.payload.ghost=false:=afterGhost
  have race : constructor.machine.dataRace=none:=afterRace
  have backend : constructor.machine.user.payload.payload.user.backend=.none:=afterBackend
  obtain ⟨updated,writeActual,_,_,_,_,write⟩:=CurrentCallBoolProtection.write_uninit_concrete options remaining span ctx constructor _ physical
    afterTracker tracked output.tag concretePhysical ghost race backend #[] selectedExtras (by simp) completed
  let post : RootState:={constructor with machine:={constructor.machine with memory:={constructor.machine.memory with live:=
    ((constructor.machine.memory.live.filter (fun row=>row.1!=physical.id)).push (physical.id,{physical.entry with allocation:=updated}))}}}
  have retag' : TypedRetag.retagPlace (config options remaining span).retag options.limits.retag place MachineHooks.protectionPolicy
      (Storage.withCurrent frames frame machine)=.ok (TypedRetagGeneric.retaggedPlace place P.id output.tag) constructor := by
    simpa only [idEq,tag,constructor] using actualRetag
  have protectActual : TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag options.limits.retag place
      (Storage.withCurrent frames frame machine)=.ok () post := by
    have retagStep:=retag'
    dsimp only [Storage.withCurrent] at retagStep
    unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
    simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,Storage.withCurrent,D.enabled,Option.isSome_some,ite_true,retagStep]
    exact writeActual
  have terminal : O.post=post:=(EStateM.Result.ok.inj (O.actual.symm.trans protectActual)).2
  have left : O.post.machine.memory.live.find? (fun row=>row.1==D.family.allocation)=
      some (D.family.allocation,⟨.machine .global,O.output.window.allocation⟩) := by
    rw [CurrentCallConversionBoolModel.memory O];exact MemoryCopyBridge.live_lookup_replaced _ _ _
  have right : post.machine.memory.live.find? (fun row=>row.1==D.family.allocation)=
      some (D.family.allocation,{physical.entry with allocation:=updated}) := by
    dsimp only [post]
    have live:=MemoryCopyBridge.live_lookup_replaced constructor.machine.memory physical.id {physical.entry with allocation:=updated}
    simpa only [idPhysical,idEq] using live
  rw [←terminal] at right
  have allocationEq : O.output.window.allocation=updated:=
    congrArg (fun row : AllocId×LocalAllocation Provenance BorrowTree MiriMemoryKind=>row.2.allocation)
      (Option.some.inj (left.symm.trans right))
  rw [←allocationEq] at write
  let writtenTree:=(physical.entry.allocation.extra.performBorrowAccessRange (.concrete output.tag)
    (Size.ofBytes physical.offset) (Size.ofBytes 1) .Write afterTracker.global.protectedTags .VisitChildrenOfAccessed).tree
  have physicalAlloc : physical.entry.allocation=result.converted.mapExtra (fun _=>output.child.tree) := by
    rw [entryPhysical,entryEq];rfl
  have inputEq : physical.entry.allocation.setExtra writtenTree=result.converted.mapExtra (fun _=>writtenTree) := by
    rw [physicalAlloc];rfl
  change Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
    (physical.entry.allocation.setExtra writtenTree)=.ok () O.output.window.allocation at write
  rw [inputEq] at write
  have byteOffset : physical.offset=D.offset:=offsetPhysical.trans offsetEq
  rw [byteOffset] at write
  exact ⟨writtenTree,write⟩

private theorem uninit_metadata {Prov Extra : Type} [DecidableEq Prov]
    (allocation updated : Allocation Prov Extra) (range : AllocRange) (pointerSize : Size)
    (actual : Allocation.writeUninit range pointerSize allocation=.ok () updated) :
    updated.byteSize=allocation.byteSize ∧updated.align=allocation.align ∧
      updated.mutability=allocation.mutability ∧updated.len=allocation.len := by
  cases allocation
  unfold Allocation.writeUninit at actual
  unfold_internal_at ".Allocation.setInitialization" at actual
  simp only [Id.run,bind,pure,Except.mapError,Bind.bind,Pure.pure,Except.bind,Except.pure] at actual
  repeat' first | split at * | contradiction
  all_goals try simp_all only [EStateM.Result.ok.injEq,Except.ok.injEq]
  all_goals cases actual <;> subst_vars <;> simp [Allocation.byteSize,Allocation.len]

theorem allocation_metadata (ctx : ActualRetagContext.Context options remaining span)
    (wiring : (CurrentCallConversionActualEnsure.hooks options).rootPointer=
      PointerSource.globalRootPointer EvalPointerSource.tape (CurrentCallConversionActualEnsure.hooks options).address externStatic)
    (O : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result) :
    O.output.window.allocation.byteSize=D.source.byteSize ∧O.output.window.allocation.align=D.source.align ∧
      O.output.window.allocation.mutability=D.source.mutability ∧O.output.window.allocation.len=D.source.len := by
  obtain ⟨tree,actual⟩:=mutation ctx wiring O
  obtain ⟨size,align,mutable,len⟩:=uninit_metadata _ _ _ _ actual
  exact ⟨size.trans result.attributes.size,align.trans result.attributes.align,
    mutable.trans result.attributes.mutability,len.trans result.attributes.storage⟩

/-- The actual materialization and uninit write preserve metadata for ALL IDs. -/
theorem getAllocInfo (ctx : ActualRetagContext.Context options remaining span)
    (wiring : (CurrentCallConversionActualEnsure.hooks options).rootPointer=
      PointerSource.globalRootPointer EvalPointerSource.tape (CurrentCallConversionActualEnsure.hooks options).address externStatic)
    (O : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result) :
    ∀id,O.post.machine.memory.getAllocInfo id=machine.memory.getAllocInfo id := by
  have sourceInfo : machine.memory.getAllocInfo D.family.allocation=.ok ⟨D.source.byteSize,D.source.align,.liveData,D.source.mutability⟩ := by
    cases D.current with
    | memory descriptor=>exact GlobalDataOnlyMaterialize.alloc_info machine _ _ D.absent D.noFunction D.noVaList descriptor
    | internalStatic definition descriptor initializer=>exact StaticGlobalAllocInfo.alloc_info machine _ _ definition D.absent D.noFunction D.noVaList descriptor
  obtain ⟨size,align,mutable,_⟩:=allocation_metadata ctx wiring O
  have known : machine.memory.getAllocInfo D.family.allocation=.ok
      ⟨O.output.window.allocation.byteSize,O.output.window.allocation.align,.liveData,O.output.window.allocation.mutability⟩ := by
    rw [size,align,mutable];exact sourceInfo
  have frame:=CurrentCallConversionMaterialize.metadata_frame machine D.family.allocation MiriMemoryKind.global O.output.window.allocation known
  intro id
  rw [CurrentCallConversionBoolModel.memory O]
  exact frame id

private theorem global_cached (memory : MemoryState Provenance BorrowTree MiriMemoryKind) (id : AllocId)
    (global : GlobalAllocation) (found : memory.findGlobal? id=some global) : memory.hasGlobalId id=true := by
  unfold MemoryState.hasGlobalId KeyedArray.contains
  rw [Std.HashMap.contains_eq_isSome_getElem?]
  unfold MemoryState.findGlobal? KeyedArray.find? at found
  simp only [bind,Bind.bind,Option.bind] at found
  split at found <;> simp_all

/-- CURRENT descriptors are metadata-live even before their heap row exists. -/
theorem isAllocLive
    (O : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result) :
    ∀id,O.post.machine.memory.isAllocLive id=machine.memory.isAllocLive id := by
  have existsGlobal : ∃global,machine.memory.findGlobal? D.family.allocation=some global := by
    cases D.current with
    | memory descriptor=>exact ⟨_,descriptor⟩
    | internalStatic definition descriptor initializer=>exact ⟨_,descriptor⟩
  obtain ⟨global,found⟩:=existsGlobal
  have known : machine.memory.isAllocLive D.family.allocation=true := by
    change _ || machine.memory.hasGlobalId D.family.allocation=true
    rw [global_cached _ _ _ found]
    simp
  have frame:=CurrentCallConversionMaterialize.live_frame machine D.family.allocation MiriMemoryKind.global O.output.window.allocation known
  intro id
  rw [CurrentCallConversionBoolModel.memory O]
  exact frame id

theorem lookup (ctx : ActualRetagContext.Context options remaining span)
    (wiring : (CurrentCallConversionActualEnsure.hooks options).rootPointer=
      PointerSource.globalRootPointer EvalPointerSource.tape (CurrentCallConversionActualEnsure.hooks options).address externStatic)
    (O : Protected (options:=options) (remaining:=remaining) (span:=span) D externStatic tail charge reserve finalAddresses finalTape result) :
    GlobalAddressLiveErrorExclusion.lookup O.post.machine.memory=GlobalAddressLiveErrorExclusion.lookup machine.memory := by
  unfold GlobalAddressLiveErrorExclusion.lookup
  congr 1 <;> funext id
  · rw [getAllocInfo ctx wiring O id]
  · rw [isAllocLive O id]

end
end DuplicatePrefix.CurrentCallConversionBoolMetadata
