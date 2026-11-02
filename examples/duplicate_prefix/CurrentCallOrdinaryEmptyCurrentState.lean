import duplicate_prefix.CurrentCallOrdinaryEmptyCurrentCopy
import duplicate_prefix.CurrentCallEmptyMaterializedSourceFacts
import duplicate_prefix.CurrentCallResourcePreparedEntry
import duplicate_prefix.GenericFunctionEntryNumerics
namespace DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CurrentCallOrdinaryInput CanonicalConfigFacts ActualReferenceContext ActualReferenceMetadata
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

def closed (options : EvalConfigurationCore.Options) (after : Before) (id : AllocId) (root : BorTag)
    (converted : Allocation Provenance Unit) (tree : BorrowTree) (global : GlobalState) (mode : RetagPolicy.RetagMode) : Before :=
  let entry : LocalAllocation Provenance BorrowTree MiriMemoryKind:=
    ⟨.machine .global,converted.mapExtra (fun _=>BorrowTree.new root converted.byteSize)⟩
  let installed:=CurrentCallConversionMaterialize.installed
    (MemoryExtras.putAllocation (GlobalDataOnlyActualConfig.extras options) after id ⟨none,#[]⟩) id .global entry.allocation
  let raw:={installed with memory:=RetagEntry.updatedMemory installed.memory id entry tree}
  {raw with borrowTracker:=some ⟨global,mode⟩,user:={raw.user with payload:={raw.user.payload with ghost:=false}}}

variable {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before} {argument : DuplicatePrefixSliceArgument.Argument}
    {place : MPlaceTy Provenance}
    (input : OrdinaryInput options limits remaining span before argument 0 place)
    (id : AllocId) (pointer : Pointer Provenance) (root : BorTag)
    (source : Allocation CtfeProvenance Unit)
    (externStatic : Miri.MIR.DefId→MachineAddress.M MiriMemoryKind CurrentCallConversionFiniteFold.Control (Pointer Provenance))
    (tail : List AllocId) (finalAddresses : Miri.Memory.AllocAddresses.GlobalAddressState) (finalTape : ExecutionChoices.Tape)
    (result : CurrentCallConversionFiniteFold.Result source PreparedReflection.actual.compiler.runtime.target.base
      (CurrentCallConversionActualEnsure.hooks options).address externStatic
      (CurrentCallOrdinaryEmptyCurrentCopy.registered input id pointer).machine
      (CurrentCallOrdinaryEmptyCurrentCopy.nextTracker input) tail (addressCharge before) 15 finalAddresses finalTape)
    (tree : BorrowTree)

theorem model : DuplicatePrefixCallModel.Model options remaining span
    (closed options result.machine id root result.converted tree result.global input.tracker.retagMode) := by
  have prepared:=CurrentCallResourcePreparedEntry.model input.model #[]
  have controlEq : (config options (remaining+1) span).terminators.getControl
      (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).user=
      (config options (remaining+1) span).terminators.getControl (CurrentCallPush.preparedMachine before #[]).user := by
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
    rfl
  refine ⟨prepared.debugOff,prepared.preciseOff,prepared.implicitOff,rfl,?_,⟨_,rfl,input.defaultMode⟩,?_,?_,?_,?_,?_,?_,prepared.nullComparator,prepared.sourceMatches⟩
  · rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact prepared.shallow
  · rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact prepared.noDataRace
  · rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact prepared.noBackend
  · rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact prepared.metadata
  · rw [result.frame,CurrentCallConversionFiniteFold.state_eq];exact prepared.fixedScheduler
  · rw [controlEq];exact prepared.unchecked
  · rw [controlEq];exact prepared.noGc

theorem types : (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).user.payload.payload.user.types=
    before.user.payload.payload.user.types := by
  rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
  rfl

theorem threads : (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).threads=
    (CurrentCallPush.preparedMachine before #[]).threads := by
  rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
  rfl

theorem addresses : (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).user.addresses=result.addresses := by
  rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
  rfl

theorem advanced : input.tracker.global.nextPointerTag.value.toNat+1≤result.global.nextPointerTag.value.toNat := by
  have advance:=result.counter
  have fresh : input.tracker.global.nextPointerTag.value<18446744073709551615 := by
    have room:=input.resources.tagRoom
    simpa [UInt64.lt_iff_toNat_lt] using (show input.tracker.global.nextPointerTag.value.toNat<18446744073709551615 by omega)
  change (TypedRetagEmpty.successorTag input.tracker.global.nextPointerTag fresh).value.toNat≤_ at advance
  rw [GenericFunctionEntryNumerics.successor_value] at advance
  exact advance

theorem protectors : ∀row∈result.global.protectedTags.entries,row.1.value.toNat<result.global.nextPointerTag.value.toNat := by
  intro row member
  rw [result.flags] at member
  change row∈((input.tracker.global.protectedTags.entries.filter (fun row=>row.1!=input.tracker.global.nextPointerTag)).push
    (input.tracker.global.nextPointerTag,.StrongProtector)) at member
  have advance:=advanced input id pointer source externStatic tail finalAddresses finalTape result
  rcases Array.mem_push.mp member with old | same
  · have prior:=input.protectorsBelow row (Array.mem_of_mem_filter old)
    omega
  · cases same
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) advance

theorem held : result.global.protectedTags.contains input.tracker.global.nextPointerTag=true := by
  rw [result.flags]
  change ((input.tracker.global.protectedTags.insert input.tracker.global.nextPointerTag .StrongProtector).contains input.tracker.global.nextPointerTag)=true
  simp [ProtectedTags.contains,ProtectedTags.insert,ProtectedTags.get]


theorem live : (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).memory.live.find? (fun row=>row.1==id)=
    some (id,⟨.machine .global,result.converted.mapExtra (fun _=>tree)⟩) := by
  exact MemoryCopyBridge.live_lookup_replaced _ _ _

theorem root_below (older : root.value.toNat<input.tracker.global.nextPointerTag.value.toNat) :
    root.value.toNat<result.global.nextPointerTag.value.toNat := by
  have advance:=advanced input id pointer source externStatic tail finalAddresses finalTape result
  omega

theorem concrete_runtime (older : root.value.toNat<input.tracker.global.nextPointerTag.value.toNat) (offset : UInt64) :
    DuplicatePrefixBorrowContract.RuntimeFacts (TypedRetagConcreteEmpty.lazyTree root input.tracker.global.nextPointerTag result.converted.byteSize.bytes) result.global := by
  have distinct : root≠input.tracker.global.nextPointerTag := by
    intro same
    have eq:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    omega
  exact CurrentCallEmptyMaterializedSourceFacts.concrete_runtime root input.tracker.global.nextPointerTag result.converted.byteSize result.global
    (root_below input id pointer root source externStatic tail finalAddresses finalTape result older)
    (protectors input id pointer source externStatic tail finalAddresses finalTape result) distinct
    (by have advance:=advanced input id pointer source externStatic tail finalAddresses finalTape result;omega)
    (held input id pointer source externStatic tail finalAddresses finalTape result) offset

theorem wildcard_runtime (older : root.value.toNat<input.tracker.global.nextPointerTag.value.toNat) (offset : UInt64) :
    DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallEmptyMaterializedWildcard.finalTree root input.tracker.global.nextPointerTag result.converted.byteSize) result.global := by
  have distinct : root≠input.tracker.global.nextPointerTag := by
    intro same
    have eq:=congrArg (fun tag : BorTag=>tag.value.toNat) same
    omega
  exact CurrentCallEmptyMaterializedSourceFacts.wildcard_runtime root input.tracker.global.nextPointerTag result.converted.byteSize result.global
    (root_below input id pointer root source externStatic tail finalAddresses finalTape result older)
    (protectors input id pointer source externStatic tail finalAddresses finalTape result) distinct
    (by have advance:=advanced input id pointer source externStatic tail finalAddresses finalTape result;omega)
    (held input id pointer source externStatic tail finalAddresses finalTape result) offset


theorem registry : (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==id)=some (id,⟨none,#[]⟩) := by
  change ((result.machine.user.payload.payload.user.runtime.extras.allocations.filter (fun row=>row.1!=id)).push (id,⟨none,#[]⟩)).find? (fun row=>row.1==id)=_
  have noMatch : result.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun _=>false)=none := by simp [Array.find?_eq_none]
  simp [Array.find?_push,Array.find?_filter,noMatch]

theorem base (base : UInt64) (cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩) :
    (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).user.addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩ := by
  rw [addresses]
  apply result.bases
  exact cached

theorem root_cache (cached : input.tracker.global.rootTag? id=some root) : result.global.rootTag? id=some root := by
  apply result.roots
  exact cached

theorem fresh : result.global.nextPointerTag.value<18446744073709551615 := by
  have budget:=result.rootBudget
  simpa [UInt64.lt_iff_toNat_lt] using (show result.global.nextPointerTag.value.toNat<18446744073709551615 by omega)


theorem concrete_eq : CurrentCallOrdinaryEmptyCurrentCopy.finalMachine options result.machine id root input.tracker.global.nextPointerTag result.converted=
    closed options result.machine id root result.converted (TypedRetagConcreteEmpty.lazyTree root input.tracker.global.nextPointerTag result.converted.byteSize.bytes) result.global .FnEntry := by
  rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
  rfl

theorem wildcard_eq : CurrentCallOrdinaryEmptyCurrentCopy.finalWildcardMachine options result.machine id root input.tracker.global.nextPointerTag result.converted=
    closed options result.machine id root result.converted (CurrentCallEmptyMaterializedWildcard.finalTree root input.tracker.global.nextPointerTag result.converted.byteSize) result.global .FnEntry := by
  rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
  rfl

theorem origins : DuplicatePrefixTypeCacheOrigins.Origins (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).user.payload.payload.user.types := by
  rw [types]
  exact input.cacheOrigins


theorem heap : (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).memory=
    (CurrentCallConversionMaterialize.installed before id .global (result.converted.mapExtra (fun _=>tree))).memory := by
  rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
  exact MemoryCopyBridge.live_update_twice _ _ _ _

theorem info (current : CurrentPayload before id source)
    (absent : before.memory.live.find? (fun row=>row.1==id)=none)
    (noFunction : before.memory.hasFunctionPointer id=false) (noVaList : before.memory.hasVaListId id=false) :
    ∀query,(closed options result.machine id root result.converted tree result.global input.tracker.retagMode).memory.getAllocInfo query=before.memory.getAllocInfo query := by
  intro query
  rw [heap]
  apply CurrentCallConversionMaterialize.metadata_frame
  change before.memory.getAllocInfo id=.ok ⟨result.converted.byteSize,result.converted.align,.liveData,result.converted.mutability⟩
  rw [result.attributes.size,result.attributes.align,result.attributes.mutability]
  cases current with
  | memory descriptor=>exact GlobalDataOnlyMaterialize.alloc_info before id source absent noFunction noVaList descriptor
  | internalStatic definition descriptor initializer=>exact StaticGlobalAllocInfo.alloc_info before id source definition absent noFunction noVaList descriptor


theorem live_other (query : AllocId) (different : query≠id) :
    (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).memory.live.find? (fun row=>row.1==query)=before.memory.live.find? (fun row=>row.1==query) := by
  rw [heap]
  exact GlobalAddressLiveSizeFormation.insert_lookup_other before.memory id query _ different

theorem extras_other (query : AllocId) (different : query≠id) :
    (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==query)=before.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==query) := by
  rw [result.frame,CurrentCallConversionFiniteFold.state_eq]
  change ((before.user.payload.payload.user.runtime.extras.allocations.filter (fun row=>row.1!=id)).push (id,⟨none,#[]⟩)).find? (fun row=>row.1==query)=_
  have unequal : (id==query)=false:=beq_eq_false_iff_ne.mpr different.symm
  simp [Array.find?_push,Array.find?_filter,unequal]
  congr 1
  funext row
  cases row with | mk key value=>
    by_cases same : key=query
    · subst key;simp [different]
    · simp [same]

theorem extras_absent (query : AllocId) (different : query≠id)
    (absent : before.user.payload.payload.user.runtime.extras.allocations.any (fun row=>row.1==query)=false) :
    (closed options result.machine id root result.converted tree result.global input.tracker.retagMode).user.payload.payload.user.runtime.extras.allocations.any (fun row=>row.1==query)=false := by
  have findNone : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==query)=none := by
    have h : (before.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==query)).isSome=false := by simpa only [Array.isSome_find?] using absent
    cases found : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row=>row.1==query) with
    | none=>rfl
    | some row=>rw [found] at h;cases h
  have same:=extras_other input id pointer root source externStatic tail finalAddresses finalTape result tree query different
  rw [findNone] at same
  simpa only [Array.isSome_find?,Option.isSome_none] using congrArg Option.isSome same


theorem cached_below (query : AllocId) (tag : BorTag) (cached : input.tracker.global.rootTag? query=some tag) :
    tag.value.toNat<input.tracker.global.nextPointerTag.value.toNat := by
  cases found : input.tracker.global.rootPointerTags.find? (fun row=>row.1==query) with
  | none=>simp only [GlobalState.rootTag?,found,Option.map_none] at cached;cases cached
  | some row=>
    have same : row.2=tag:=Option.some.inj (by simpa only [GlobalState.rootTag?,found,Option.map_some] using cached)
    have below:=input.resources.cachedRootsBelow row (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some found))
    rw [same] at below
    exact below

end
end DuplicatePrefix.CurrentCallOrdinaryEmptyCurrentState
