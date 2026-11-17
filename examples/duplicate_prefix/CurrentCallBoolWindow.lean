import duplicate_prefix.CurrentCallReferenceEntry
import duplicate_prefix.CandidateCurrentBoolUninitWrite
import duplicate_prefix.S03UninitMetadata

/-! Physical Bool windows survive source retagging and tree-only installation.
No post-state ownership packet or initialized old Bool value is required. -/
namespace DuplicatePrefix.CurrentCallBoolWindow
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallReferenceEntry
open CandidateCurrentBoolUninitWrite
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def tree_only {before : Before} {place : MPlaceTy Provenance}
    (input : PhysicalWindow before place) (after : Before) (tree : BorrowTree)
    (addresses : after.user.addresses = before.user.addresses)
    (present : after.memory.live.find? (fun row => row.1 == input.id) =
      some (input.id,{input.entry with allocation := input.entry.allocation.setExtra tree})) :
    PhysicalWindow after place :=
  {input with entry := {input.entry with allocation := input.entry.allocation.setExtra tree}
              live := present
              cachedBase := by rw [addresses];exact input.cachedBase}

def retagged {before : Before} {place : MPlaceTy Provenance}
    (input : PhysicalWindow before place) (after : Before) (tree : BorrowTree) (tag : BorTag)
    (addresses : after.user.addresses = before.user.addresses)
    (present : after.memory.live.find? (fun row => row.1 == input.id) =
      some (input.id,{input.entry with allocation := input.entry.allocation.setExtra tree})) :
    PhysicalWindow after (TypedRetagGeneric.retaggedPlace place input.id tag) :=
  {tree_only input after tree addresses present with
    pointer := ⟨input.pointer.offset,.concrete input.id tag⟩
    physicalPointer := by rw [TypedRetagGeneric.retaggedPlace,input.physicalPointer];rfl}

def after {options remaining span ctx before tracker frames frame borrowFrame argument len place call data}
    (source : ViewedOutcome options remaining span ctx before tracker frames frame borrowFrame argument len place call data .FnEntry true) : Before :=
  {validatedMachine source with borrowTracker := some ⟨source.base.raw.output.global,tracker.retagMode⟩}

/-- Physical support after the protection consumer's tree-only installation.
Only the temporary pointer gains the fresh concrete child provenance. -/
noncomputable def protected_window {before : Before} {place : MPlaceTy Provenance}
    (input : PhysicalWindow before place)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (tree : BorrowTree) :
    PhysicalWindow
      (ReturnProtection.borrowedState frames frame borrowFrame before tracker room input.id input.entry tree).machine
      (TypedRetagGeneric.retaggedPlace place input.id tracker.global.nextPointerTag) :=
  retagged input _ tree tracker.global.nextPointerTag rfl
    (MemoryCopyBridge.live_lookup_replaced before.memory input.id _)

theorem initial (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data) :
    ∃ physical : PhysicalWindow before place, physical.id = call.returnId ∧
      physical.offset = UInt64.ofNat call.returnOffset ∧
      CandidateCallBindings.WindowBinding before physical.pointer call.returnId call.returnOffset 1 := by
  obtain ⟨layout,pointer,placeEq,loan,pointerInstance,loanAt,pointerAt,valueEq,idEq,window⟩ := input.actual.returnAddress
  obtain ⟨entry,base,live,cached,bytes,room,bounds,address,nonnull,provenance⟩ := window
  have offsetBound : call.returnOffset < 2^64 := by omega
  have offsetEq : (UInt64.ofNat call.returnOffset).toNat = call.returnOffset := by
    simp [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetBound]
  have addressEq : pointer.offset.bytes = base+UInt64.ofNat call.returnOffset := by
    apply UInt64.toNat_inj.mp
    rw [address,UInt64.toNat_add,offsetEq,Nat.mod_eq_of_lt (by omega : base.toNat+call.returnOffset<2^64)]
  obtain ⟨allocation,allocationAt,physical⟩ := input.actual.returnValue
  have entryAt : Present (ActualWorld before) call.returnId entry.allocation := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(call.returnId,entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
  have same := CandidateCurrentUniformOwnerWindow.same_id _ input.machine.worldIds call.returnId allocation entry.allocation
    allocationAt entryAt
  subst allocation
  let result : PhysicalWindow before place := {
    pointer := pointer,physicalPointer := placeEq,layout := layout,aligned := input.actual.returnAligned
    id := call.returnId,entry := entry,base := base,offset := UInt64.ofNat call.returnOffset
    capacity := entry.allocation.byteSize.bytes,live := live,cachedBase := cached,pointerAddress := addressEq
    bounds := by rw [offsetEq];omega
    size := rfl,bytes := bytes,mutable := physical.writable,maskValid := physical.storage.maskCapacity
    maskLength := physical.storage.maskLength,provenanceMap := physical.storage.provenance }
  exact ⟨result,rfl,rfl,entry,base,live,cached,bytes,room,bounds,address,nonnull,provenance⟩

private theorem optional_injective (left right : Pointer Provenance)
    (equal : left.withOptionalProvenance = right.withOptionalProvenance) : left = right := by
  cases left
  cases right
  simp_all [Pointer.withOptionalProvenance]

theorem after_source (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (source : ViewedOutcome options remaining span ctx before tracker frames frame borrowFrame argument len place call data .FnEntry true) :
    ∃ physical : PhysicalWindow (after source) place, physical.id = call.returnId ∧
      physical.pointer = source.base.raw.returnPointer.value ∧
      physical.offset = UInt64.ofNat call.returnOffset ∧
      CandidateCallBindings.WindowBinding (after source) source.base.raw.returnPointer.value call.returnId call.returnOffset 1 := by
  obtain ⟨original,idEq,offsetEq,window⟩ := initial options limits remaining span before tracker argument len place call data input
  have pointerEq := optional_injective original.pointer source.base.raw.returnPointer.value
    (original.physicalPointer.symm.trans source.base.raw.place_eq)
  have addresses : (after source).user.addresses = before.user.addresses := rfl
  obtain ⟨entry,base,live,cached,bytes,room,bounds,address,nonnull,provenance⟩ := window
  have entryEq : entry = original.entry := by
    have oldLive := original.live
    rw [idEq] at oldLive
    exact (Prod.mk.inj (Option.some.inj (live.symm.trans oldLive))).2
  subst entry
  by_cases same : call.sourceId = original.id
  · have sourceEntryEq : source.base.entry = original.entry := by
      have sourceLive := source.base.sourceLive
      rw [same] at sourceLive
      exact (Prod.mk.inj (Option.some.inj (sourceLive.symm.trans original.live))).2
    have present : (after source).memory.live.find? (fun row => row.1 == original.id) =
        some (original.id,{original.entry with allocation := original.entry.allocation.setExtra source.base.raw.output.child.tree}) := by
      change (RetagEntry.updatedMemory before.memory call.sourceId source.base.entry source.base.raw.output.child.tree).live.find? _ = _
      rw [same,sourceEntryEq]
      exact MemoryCopyBridge.live_lookup_replaced before.memory original.id _
    let result := tree_only original (after source) source.base.raw.output.child.tree addresses present
    refine ⟨result,idEq,pointerEq,offsetEq,?_⟩
    rw [←pointerEq]
    refine ⟨{original.entry with allocation := original.entry.allocation.setExtra source.base.raw.output.child.tree},base,?_,cached,bytes,room,bounds,address,nonnull,?_⟩
    · rw [←idEq];exact present
    · exact provenance
  · have present : (after source).memory.live.find? (fun row => row.1 == original.id) = some (original.id,original.entry) := by
      change ((before.memory.live.filter fun row => row.1 != call.sourceId).push
        (call.sourceId,{source.base.entry with allocation := source.base.entry.allocation.setExtra source.base.raw.output.child.tree})).find? _ = _
      rw [Array.find?_push,Array.find?_filter]
      have predicate : (fun row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind =>
          decide ((row.1 != call.sourceId) = true ∧ (row.1 == original.id) = true)) =
          (fun row => row.1 == original.id) := by
        funext row
        by_cases hit : row.1 = original.id
        · simp [hit,Ne.symm same]
        · simp [hit]
      rw [predicate,original.live]
      simp [same]
    let result : PhysicalWindow (after source) place := {original with live := present,cachedBase := original.cachedBase}
    refine ⟨result,idEq,pointerEq,offsetEq,?_⟩
    rw [←pointerEq]
    exact ⟨original.entry,base,by rw [←idEq];exact present,cached,bytes,room,bounds,address,nonnull,provenance⟩

theorem replace_binding (before final : Before) (pointer : Pointer Provenance)
    (id : AllocId) (offset length : Nat)
    (binding : CandidateCallBindings.WindowBinding before pointer id offset length)
    (replaceId : AllocId) (oldEntry nextEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (oldLive : before.memory.live.find? (fun row => row.1 == replaceId) = some (replaceId,oldEntry))
    (bytes : nextEntry.allocation.len = oldEntry.allocation.len)
    (size : nextEntry.allocation.byteSize = oldEntry.allocation.byteSize)
    (addresses : final.user.addresses = before.user.addresses)
    (memory : final.memory.live = (before.memory.live.filter (fun row => row.1 != replaceId)).push (replaceId,nextEntry)) :
    CandidateCallBindings.WindowBinding final pointer id offset length := by
  obtain ⟨entry,base,live,cached,byteLength,room,bounds,address,nonnull,provenance⟩ := binding
  by_cases same : replaceId = id
  · subst replaceId
    have entryEq : oldEntry = entry := (Prod.mk.inj (Option.some.inj (oldLive.symm.trans live))).2
    subst oldEntry
    refine ⟨nextEntry,base,?_,?_,?_,?_,?_,address,nonnull,?_⟩
    · rw [memory];exact MemoryCopyBridge.live_lookup_replaced before.memory id nextEntry
    · rw [addresses];exact cached
    · rw [bytes,size];exact byteLength
    · rw [bytes];exact room
    · rw [bytes];exact bounds
    · rw [addresses,size];exact provenance
  · refine ⟨entry,base,?_,?_,byteLength,room,bounds,address,nonnull,?_⟩
    · rw [memory,Array.find?_push,Array.find?_filter]
      have predicate : (fun row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind =>
          decide ((row.1 != replaceId) = true ∧ (row.1 == id) = true)) = (fun row => row.1 == id) := by
        funext row
        by_cases hit : row.1 = id
        · simp [hit,Ne.symm same]
        · simp [hit]
      rw [predicate,live]
      simp [same]
    · rw [addresses];exact cached
    · rw [addresses];exact provenance

theorem concrete_binding (before : Before) (pointer : Pointer Provenance)
    (id : AllocId) (offset length : Nat) (tag : BorTag)
    (binding : CandidateCallBindings.WindowBinding before pointer id offset length) :
    CandidateCallBindings.WindowBinding before (CurrentCallTypedFnEntry.changedPointer pointer id tag) id offset length := by
  obtain ⟨entry,base,live,cached,byteLength,room,bounds,address,nonnull,_⟩ := binding
  exact ⟨entry,base,live,cached,byteLength,room,bounds,address,nonnull,rfl⟩

theorem source_after_write (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (source : ViewedOutcome options remaining span ctx before tracker frames frame borrowFrame argument len place call data .FnEntry true)
    (positive : 0 < len.toNat) (physical : PhysicalWindow (after source) place)
    (updated : Allocation Provenance BorrowTree) (final : Before)
    (bytes : updated.len = physical.entry.allocation.len)
    (size : updated.byteSize = physical.entry.allocation.byteSize)
    (addresses : final.user.addresses = (after source).user.addresses)
    (memory : final.memory.live = ((after source).memory.live.filter (fun row => row.1 != physical.id)).push
      (physical.id,{physical.entry with allocation := updated})) :
    CandidateCallBindings.WindowBinding final
      (CurrentCallTypedFnEntry.changedPointer source.base.raw.sourcePointer.value call.sourceId tracker.global.nextPointerTag)
      call.sourceId call.sourceOffset len.toNat := by
  have original : CandidateCallBindings.WindowBinding before source.base.raw.sourcePointer.value call.sourceId call.sourceOffset len.toNat := by
    rcases input.actual.sourceAddress with empty | ⟨_,pointer,argumentEq,loan,pointerInstance,loanAt,pointerAt,valueEq,idEq,window⟩
    · simp [empty.1] at positive
    have same : pointer = source.base.raw.sourcePointer.value :=
      DuplicatePrefixSliceArgument.Argument.pointer.inj (argumentEq.symm.trans source.base.raw.argument_eq)
    rw [same,input.actual.length] at window
    exact window
  have installed := replace_binding before (after source) source.base.raw.sourcePointer.value call.sourceId call.sourceOffset len.toNat
    original call.sourceId source.base.entry
    {source.base.entry with allocation := source.base.entry.allocation.setExtra source.base.raw.output.child.tree}
    source.base.sourceLive rfl rfl rfl rfl
  have changed := concrete_binding (after source) source.base.raw.sourcePointer.value call.sourceId call.sourceOffset len.toNat
    tracker.global.nextPointerTag installed
  exact replace_binding (after source) final _ call.sourceId call.sourceOffset len.toNat changed
    physical.id physical.entry {physical.entry with allocation := updated} physical.live bytes size addresses memory

theorem mutation_metadata {before : Before} {place : MPlaceTy Provenance}
    (physical : PhysicalWindow before place) (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
    (actual : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1))
      (Size.ofBytes 8) (physical.entry.allocation.setExtra tree) = .ok () updated) :
    updated.len = physical.entry.allocation.len ∧ updated.byteSize = physical.entry.allocation.byteSize ∧
    updated.mutability = .Mut ∧ updated.extra = tree ∧
    InitMaskCopy.WellFormed updated.initializationMask ∧
    updated.initializationMask.len = updated.byteSize ∧
    ProvenanceMap.clear (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1))
      (AllocationCopy.snapshot (physical.entry.allocation.setExtra tree)) (Size.ofBytes 8)
      physical.entry.allocation.provenanceMap = .ok () updated.provenanceMap := by
  obtain ⟨expected,mutation,length,bytes,mutable,extra,maskWF,maskLen,clear⟩ :=
    S03UninitMetadata.uninit (physical.entry.allocation.setExtra tree) physical.capacity physical.offset
      physical.bytes physical.size physical.mutable physical.maskValid physical.maskLength physical.provenanceMap physical.bounds
  have equal : expected = updated := (EStateM.Result.ok.inj (mutation.symm.trans actual)).2
  subst expected
  exact ⟨length,bytes,mutable,extra,maskWF,by rw [maskLen,bytes];exact physical.maskLength.trans physical.size.symm,clear⟩

theorem source_allocation_after_write (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument len place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (source : ViewedOutcome options remaining span ctx before tracker frames frame borrowFrame argument len place call data .FnEntry true)
    (positive : 0 < len.toNat) (physical : PhysicalWindow (after source) place) (idEq : physical.id = call.returnId)
    (tree : BorrowTree) (updated : Allocation Provenance BorrowTree) (final : Before)
    (actual : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1))
      (Size.ofBytes 8) (physical.entry.allocation.setExtra tree) = .ok () updated)
    (memory : final.memory.live = ((after source).memory.live.filter (fun row => row.1 != physical.id)).push
      (physical.id,{physical.entry with allocation := updated})) :
    ∃ entry, final.memory.live.find? (fun row => row.1 == call.sourceId) = some (call.sourceId,entry) ∧
      entry.allocation.extra = (if call.sourceId = call.returnId then tree else source.base.raw.output.child.tree) ∧
      entry.allocation.byteSize = source.base.raw.sourceAllocation.byteSize ∧
      entry.allocation.len = source.base.raw.sourceAllocation.len ∧ entry.allocation.mutability = .Mut ∧
      InitMaskCopy.WellFormed entry.allocation.initializationMask ∧
      entry.allocation.initializationMask.len = entry.allocation.byteSize ∧
      (call.sourceId = call.returnId → entry.allocation = updated) ∧
      (call.sourceId ≠ call.returnId → entry.allocation = source.base.entry.allocation.setExtra source.base.raw.output.child.tree) := by
  have sourceLive : (after source).memory.live.find? (fun row => row.1 == call.sourceId) =
      some (call.sourceId,{source.base.entry with allocation := source.base.entry.allocation.setExtra source.base.raw.output.child.tree}) :=
    source.sourceInstalled
  have sourcePhysical : OrdinaryPhysicalValidity.MutU8Slice source.base.entry.allocation (UInt64.ofNat call.sourceOffset) len := by
    rcases input.actual.sourceValue with ⟨zero,_⟩ | ⟨_,allocation,present,physical⟩
    · simp [zero] at positive
    have same := CandidateCurrentUniformOwnerWindow.same_id _ input.machine.worldIds call.sourceId allocation source.base.raw.sourceAllocation
      present source.base.raw.sourcePresent
    rw [same,←source.base.sourceAllocation] at physical
    exact physical
  obtain ⟨length,bytes,mutable,extra,maskWF,maskLen,clear⟩ := mutation_metadata physical tree updated actual
  by_cases same : call.sourceId = call.returnId
  · have physicalId : physical.id = call.sourceId := idEq.trans same.symm
    have entryEq : physical.entry = {source.base.entry with allocation := source.base.entry.allocation.setExtra source.base.raw.output.child.tree} := by
      have live := physical.live
      rw [physicalId] at live
      exact (Prod.mk.inj (Option.some.inj (live.symm.trans sourceLive))).2
    refine ⟨{physical.entry with allocation := updated},?_,?_,?_,?_,mutable,maskWF,maskLen,by intro _;rfl,by simp [same]⟩
    · rw [memory,physicalId];exact MemoryCopyBridge.live_lookup_replaced (after source).memory call.sourceId _
    · simp only [same,ite_true];exact extra
    · rw [bytes,entryEq];change source.base.entry.allocation.byteSize = _
      exact congrArg Allocation.byteSize source.base.sourceAllocation
    · rw [length,entryEq];change source.base.entry.allocation.len = _
      exact congrArg Allocation.len source.base.sourceAllocation
  · have different : physical.id ≠ call.sourceId := by rw [idEq];exact Ne.symm same
    refine ⟨{source.base.entry with allocation := source.base.entry.allocation.setExtra source.base.raw.output.child.tree},?_,?_,?_,?_,
      sourcePhysical.writable,sourcePhysical.storage.maskCapacity,sourcePhysical.storage.maskLength,by simp [same],by intro _;rfl⟩
    · rw [memory,Array.find?_push,Array.find?_filter]
      have predicate : (fun row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind =>
          decide ((row.1 != physical.id) = true ∧ (row.1 == call.sourceId) = true)) = (fun row => row.1 == call.sourceId) := by
        funext row
        by_cases hit : row.1 = call.sourceId
        · simp [hit,Ne.symm different]
        · simp [hit]
      rw [predicate,sourceLive];simp [different]
    · simp only [same,ite_false];rfl
    · change source.base.entry.allocation.byteSize = _
      exact congrArg Allocation.byteSize source.base.sourceAllocation
    · change source.base.entry.allocation.len = _
      exact congrArg Allocation.len source.base.sourceAllocation

end DuplicatePrefix.CurrentCallBoolWindow

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallBoolWindow." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current Bool window dependency {dependency}"
