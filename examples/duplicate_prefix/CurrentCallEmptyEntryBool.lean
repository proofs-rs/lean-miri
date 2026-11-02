import duplicate_prefix.CurrentCallEmptyEntryArguments
import duplicate_prefix.CurrentCallBoolProtection
import duplicate_prefix.CurrentCallEmptyEntryRootLoop
import duplicate_prefix.CurrentCallEmptyEntryZeroRootQueries
import duplicate_prefix.S05WildcardProtectedRootCompletion
import duplicate_prefix.CurrentCallEmptyEntryBoolChildNormal
import duplicate_prefix.CurrentCallEmptyEntrySifaWrite
import duplicate_prefix.CurrentCallEmptyEntryConcreteZero
import duplicate_prefix.S04ZeroWildcardRuntime
import duplicate_prefix.GeneralBorrowSharedReadConstructor
import duplicate_prefix.CurrentCallEmptyEntryWriteRetention
import duplicate_prefix.CurrentCallEmptyEntryNormalWrite
import duplicate_prefix.CurrentCallEmptyEntryWriteKind
import duplicate_prefix.GeneralBorrowConstructorChildActivity
import duplicate_prefix.GeneralBorrowFreshActiveWithinAccess
import duplicate_prefix.CurrentCallEmptyEntryQuietRelease
import duplicate_prefix.CurrentCallEmptyEntryBoolRelease
import duplicate_prefix.CurrentCallEmptyEntryCompleteRelease
import duplicate_prefix.CurrentCallRootRelease
import duplicate_prefix.CurrentCallEmptyEntryQuietCompleteBorrow
import duplicate_prefix.CurrentCallEmptyEntrySourceData
import duplicate_prefix.CurrentCallEmptyEntryCompleteHoldings
import duplicate_prefix.CurrentCallEmptyEntryRepairedMetadata
import duplicate_prefix.CurrentCallEmptyEntryHiddenFrame

/-! Bool-only entry support after exact empty source effects. The original
return owner supplies the nonempty byte; empty sources impose no content loan. -/
namespace DuplicatePrefix.CurrentCallEmptyEntryBool
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
open GeneralBorrowWildcardParentTagOrder GeneralRangeMapOrigins GeneralBorrowExposureCardinality Miri.DataStructures
open TypedBorrowSteps ReferenceBorrowDriver
open OrdinaryBorrowAuthority
open S05CompletedAncestryReadMutable (Authority)
open DuplicatePrefix.BorrowRangeAccess GeneralBorrowProjection GeneralBorrowView GeneralBorrowNodeUpdate GeneralBorrowPresence GeneralBorrowFreshNode
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
attribute [local irreducible] UniValMap.insert

private structure ReturnData (before : Before) (tracker : MachineHooks.BorrowState)
    (place : MPlaceTy Provenance) (call : CallLoans) where
  physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place
  pointer : PointerInstance
  precise : PreciseAllocation
  id : physical.id = call.returnId
  offset : physical.offset = UInt64.ofNat call.returnOffset
  offsetNat : physical.offset.toNat = call.returnOffset
  pointerEq : physical.pointer = pointer.value
  pointerId : pointer.allocation = call.returnId
  binding : CandidateCallBindings.WindowBinding before pointer.value call.returnId call.returnOffset 1
  node : TreeNode
  present : physical.entry.allocation.extra.nodes.get pointer.grant = some node
  provenance : match pointer.value.provenance with
    | .concrete _ tag => tag = node.tag
    | .wildcard => node.isExposed = true
  runtime : DuplicatePrefixBorrowContract.RuntimeFacts physical.entry.allocation.extra tracker.global
  completes : Completes physical.entry.allocation.extra precise.completion
  order : ParentTagOrder physical.entry.allocation.extra
  owned : OwnedOn (Authority physical.entry.allocation.extra precise.completion tracker.global.protectedTags pointer.grant)
    (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) physical.entry.allocation.extra.locations
  bounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ physical.entry.allocation.extra.locations.size.bytes.toNat
  room : physical.entry.allocation.extra.nodes.size+1 ≤ 4294967295
  short : physical.entry.allocation.extra.nodes.size < 65536

private theorem return_data {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data) :
    Nonempty (ReturnData before tracker place call) := by
  obtain ⟨loan,pointer,allocation,precise,loanAt,pointerAt,pointerId,allocationAt,preciseAt,rights⟩ :=
    CandidateCurrentUniformOwnerWindow.uniform_window (ActualWorld before) tracker.global.protectedTags data.interpretation
      input.joint call.returnOwner call.returnId call.returnOffset 1 .ret (by decide)
      (fun byte inside => (input.contents.returnContents byte).mpr inside)
  obtain ⟨physical,idEq,offsetEq,window⟩ := CurrentCallBoolWindow.initial options limits remaining span before tracker argument 0 place call data input
  have physicalAt : Present (ActualWorld before) call.returnId physical.entry.allocation := by
    rw [←idEq]
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(physical.id,physical.entry),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some physical.live),rfl⟩
  have allocationEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList input.machine.worldIds
    call.returnId allocation physical.entry.allocation allocationAt physicalAt
  subst allocation
  obtain ⟨_,bits,placeEq,boundLoan,boundPointer,boundLoanAt,boundPointerAt,valueEq,_,boundWindow⟩ := input.actual.returnAddress
  have loanEq := Option.some.inj (boundLoanAt.symm.trans loanAt)
  subst boundLoan
  have pointerEqual := Option.some.inj (boundPointerAt.symm.trans pointerAt)
  subst boundPointer
  have pointerEq : physical.pointer = pointer.value := by
    have eq : physical.pointer.withOptionalProvenance = pointer.value.withOptionalProvenance :=
      physical.physicalPointer.symm.trans (placeEq.trans (congrArg Pointer.withOptionalProvenance valueEq.symm))
    have injective : ∀ left right : Pointer Provenance, left.withOptionalProvenance = right.withOptionalProvenance → left = right := by
      intro left right equal
      cases left
      cases right
      simpa only [Pointer.withOptionalProvenance,Pointer.mk.injEq,Option.some.injEq] using equal
    exact injective physical.pointer pointer.value eq
  have binding : CandidateCallBindings.WindowBinding before pointer.value call.returnId call.returnOffset 1 := by
    rw [pointerEq] at window
    exact window
  obtain ⟨other,otherAt,binds⟩ := input.actual.instances pointer
    (Array.mem_toList_iff.mpr (Array.mem_of_getElem? pointerAt))
  rw [pointerId] at otherAt
  have otherEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList input.machine.worldIds
    call.returnId other physical.entry.allocation otherAt physicalAt
  subst other
  obtain ⟨node,present,_,provenance⟩ := binds
  have provenanceFact : match pointer.value.provenance with
      | .concrete _ tag => tag = node.tag
      | .wildcard => node.isExposed = true := by
    cases kind : pointer.value.provenance with
    | concrete id tag =>
      simp only [kind] at provenance
      exact provenance.2
    | wildcard => simpa only [kind] using provenance
  obtain ⟨shape,shapeAt,complete,_⟩ := input.machine.completed call.returnId precise preciseAt
  have shapeEq := CandidateCurrentUniformOwnerWindow.same_id (ActualWorld before).toList input.machine.worldIds
    call.returnId shape physical.entry.allocation shapeAt physicalAt
  subst shape
  obtain ⟨runtime,order,room,short,storage,capacity⟩ := CandidateCurrentLiveRuntime.live options limits remaining before tracker 0
    input.machine.state input.machine.resources call.returnId physical.entry.allocation physicalAt
  obtain ⟨bound,offsetNat,_,sum,owned⟩ := CandidateCurrentWindowAuthority.nat_window physical.entry.allocation
    tracker.global.protectedTags precise pointer call.returnId call.returnOffset 1 .ret (by decide) (by decide)
    runtime.formed.well storage rights
  have bounds : (UInt64.ofNat call.returnOffset).toNat+1 ≤ physical.entry.allocation.extra.locations.size.bytes.toNat := by
    rw [offsetNat,capacity]
    exact bound
  exact ⟨⟨physical,pointer,precise,idEq,offsetEq,by rw [offsetEq,offsetNat],pointerEq,pointerId,binding,node,present,provenanceFact,
    runtime,complete,order,owned,bounds,room,short⟩⟩




private def boolTree {options before tracker argument} (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (id : AllocId) (old : BorrowTree) : BorrowTree :=
  match effect with
  | .concreteLive _ source _ _ tree .. => if source = id then tree else old
  | .wildcardLive _ hit _ tree .. => if hit.id = id then tree else old
  | _ => old

private theorem replaced_other {α : Type} (rows : Array (AllocId × α))
    (id other : AllocId) (value original : α)
    (different : id ≠ other) (live : rows.find? (fun row => row.1 == other) = some (other,original)) :
    ((rows.filter fun row => row.1 != id).push (id,value)).find? (fun row => row.1 == other) = some (other,original) := by
  rw [Array.find?_push,Array.find?_filter]
  have predicate : (fun row : AllocId × α =>
      decide ((row.1 != id) = true ∧ (row.1 == other) = true)) = (fun row => row.1 == other) := by
    funext row
    by_cases hit : row.1 = other
    · simp [hit,Ne.symm different]
    · simp [hit]
  rw [predicate,live]
  simp [different]

private theorem effect_addresses {options before tracker argument} (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size) :
    (CurrentCallEmptyTypedEntry.resultMachine effect fresh remaining span frames frame borrowFrame localId valid).user.addresses = before.user.addresses := by
  cases effect <;> rfl

private theorem effect_bool_live {options before tracker argument} (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    (CurrentCallEmptyTypedEntry.resultMachine effect fresh remaining span frames frame borrowFrame localId valid).memory.live.find?
      (fun row => row.1 == id) = some (id,{entry with allocation := entry.allocation.setExtra (boolTree effect id entry.allocation.extra)}) := by
  cases effect with
  | integer => exact live
  | miss => exact live
  | concreteNonlive => exact live
  | wildcardNonlive => exact live
  | concreteLive address source parent sourceEntry tree sourceLive child =>
    by_cases same : source = id
    · subst source
      have entryEq := (Prod.mk.inj (Option.some.inj (sourceLive.symm.trans live))).2
      subst sourceEntry
      simp only [boolTree]
      exact MemoryCopyBridge.live_lookup_replaced before.memory id _
    · simp only [boolTree,ite_eq_right same]
      exact replaced_other before.memory.live source id _ entry same live
  | wildcardLive address hit sourceEntry tree sourceLive child =>
    by_cases same : hit.id = id
    · have entryEq := (Prod.mk.inj (Option.some.inj ((same ▸ sourceLive).symm.trans live))).2
      subst sourceEntry
      simp only [boolTree,ite_eq_left same]
      change (RetagEntry.updatedMemory before.memory hit.id entry tree).live.find? _ = _
      rw [same]
      exact MemoryCopyBridge.live_lookup_replaced before.memory id _
    · simp only [boolTree,ite_eq_right same]
      exact replaced_other before.memory.live hit.id id _ entry same live
  | concreteImage address source parent image data converted descriptor attributes =>
    have different : source ≠ id := by
      obtain ⟨_,_,absent,_⟩ := image
      intro same
      rw [same,live] at absent
      cases absent
    simp only [boolTree]
    apply replaced_other _ source id _ entry different
    exact replaced_other before.memory.live source id _ entry different live
  | wildcardImage address hit image root data converted rootCached descriptor attributes =>
    have different : hit.id ≠ id := by
      obtain ⟨_,_,absent,_⟩ := image
      intro same
      rw [same,live] at absent
      cases absent
    simp only [boolTree]
    apply replaced_other _ hit.id id _ entry different
    exact replaced_other before.memory.live hit.id id _ entry different live


private theorem effect_source_leaf {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (same : effect.allocation = some id) :
    CurrentCallEmptyEntrySourceData.Leaf (boolTree effect id entry.allocation.extra) tracker.global.nextPointerTag := by
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  have actual := effect_bool_live effect fresh remaining span frames frame {} localId valid id entry live
  have data := CurrentCallEmptyEntrySourceData.of_effect input effect frames frame {} localId valid
  change CurrentCallEmptyEntrySourceData.Data effect _ at data
  simp only [CurrentCallEmptyEntrySourceData.Data,same] at data
  rcases data with ⟨info,lookup,notLive⟩ | ⟨found,lookup,leaf⟩
  · have actualInfo := MemoryCopyBridge.live_alloc_info _ id _ actual
    have eqInfo := Except.ok.inj (lookup.symm.trans actualInfo)
    subst info
    exact False.elim (notLive rfl)
  · have sameEntry := (Prod.mk.inj (Option.some.inj (lookup.symm.trans actual))).2
    subst found
    exact leaf

private theorem binding_after_effect {options before tracker argument} (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (pointer : Pointer Provenance) (id : AllocId) (offset length : Nat)
    (binding : CandidateCallBindings.WindowBinding before pointer id offset length) :
    CandidateCallBindings.WindowBinding
      (CurrentCallEmptyTypedEntry.resultMachine effect fresh remaining span frames frame borrowFrame localId valid)
      pointer id offset length := by
  obtain ⟨entry,base,live,cached,bytes,room,bounds,address,nonnull,provenance⟩ := binding
  let next := {entry with allocation := entry.allocation.setExtra (boolTree effect id entry.allocation.extra)}
  have addresses := effect_addresses effect fresh remaining span frames frame borrowFrame localId valid
  have byteSize : next.allocation.byteSize = entry.allocation.byteSize := by rfl
  refine ⟨next,base,effect_bool_live effect fresh remaining span frames frame borrowFrame localId valid id entry live,?_,bytes,room,bounds,address,nonnull,?_⟩
  · rw [addresses]
    exact cached
  · cases kind : pointer.provenance with
    | concrete supplied tag => simpa only [kind] using provenance
    | wildcard => simpa only [kind,addresses,byteSize] using provenance

private theorem physical_after_effect {options before tracker argument place} (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place) :
    ∃ result : CandidateCurrentBoolUninitWrite.PhysicalWindow
      (CurrentCallEmptyTypedEntry.resultMachine effect fresh remaining span frames frame borrowFrame localId valid) place,
      result.id = physical.id ∧ result.pointer = physical.pointer ∧ result.offset = physical.offset ∧
      result.entry.allocation.extra = boolTree effect physical.id physical.entry.allocation.extra := by
  let result := CurrentCallBoolWindow.tree_only physical
    (CurrentCallEmptyTypedEntry.resultMachine effect fresh remaining span frames frame borrowFrame localId valid)
    (boolTree effect physical.id physical.entry.allocation.extra)
    (effect_addresses effect fresh remaining span frames frame borrowFrame localId valid)
    (effect_bool_live effect fresh remaining span frames frame borrowFrame localId valid physical.id physical.entry physical.live)
  exact ⟨result,rfl,rfl,rfl,rfl⟩



private theorem extras_after_effect {options before tracker argument} (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (extra : MemoryExtras.AllocationExtra Unit)
    (present : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == id) = some (id,extra)) :
    (CurrentCallEmptyTypedEntry.resultMachine effect fresh remaining span frames frame borrowFrame localId valid).user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == id) = some (id,extra) := by
  cases effect with
  | integer | miss | concreteLive | concreteNonlive | wildcardLive | wildcardNonlive => exact present
  | concreteImage address source parent image data converted descriptor attributes =>
    have different : source ≠ id := by
      obtain ⟨_,_,absent,_⟩ := image
      intro same
      rw [same,live] at absent
      cases absent
    exact replaced_other before.user.payload.payload.user.runtime.extras.allocations source id _ extra different present
  | wildcardImage address hit image root data converted rootCached descriptor attributes =>
    have different : hit.id ≠ id := by
      obtain ⟨_,_,absent,_⟩ := image
      intro same
      rw [same,live] at absent
      cases absent
    exact replaced_other before.user.payload.payload.user.runtime.extras.allocations hit.id id _ extra different present

private theorem window_ready_after_effect {options before tracker argument} (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (live : before.memory.live.find? (fun row => row.1 == id) = some (id,entry)) (offset length : Nat)
    (ready : CurrentCallBoolProtection.WindowReady before id offset length) :
    CurrentCallBoolProtection.WindowReady (CurrentCallEmptyTypedEntry.resultMachine effect fresh remaining span frames frame borrowFrame localId valid) id offset length := by
  obtain ⟨sync,present,outside⟩ := ready
  exact ⟨sync,extras_after_effect effect fresh remaining span frames frame borrowFrame localId valid id entry live ⟨none,sync⟩ present,outside⟩


private theorem zero_root_owned (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (held : ProtectedTags) (complete : Completes tree completion)
    (target : UniIndex) (targetLive : ∃ node,tree.nodes.get target = some node)
    (lower upper : UInt64) (clean : GeneralBorrowFreshFutureClean.Clean tree slot.index)
    (owned : OwnedOn (Authority tree completion held target) lower upper tree.locations) :
    OwnedOn (Authority (slot.after tag) (S05ConcreteProtectedChildCompletion.extend completion slot.index target) held target)
      lower upper (slot.after tag).locations := by
  intro cursor valid positive start stop index node present
  have original := owned cursor valid positive start stop
  have ancestry := S05ConcreteProtectedChildCompletion.old_ancestry_iff tree completion complete slot.index target slot.vacant targetLive (ancestor := index)
  by_cases fresh : index = slot.index
  · subst index
    have nodeEq : node = WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None :=
      Option.some.inj (present.symm.trans (GeneralBorrowFreshLocation.get_same _ _ _))
    subst node
    have empty : (slot.after tag).locations.entries[cursor].data.perms.get slot.index = none := clean cursor valid
    constructor <;> intro _ <;>
      simp [CandidateStableCallOwnership.RawState,empty,WildcardHitZeroConstructor.rootNode,TreeNode.defaultLocationState,
        OrdinaryBorrowAuthority.LocalWrite,OrdinaryBorrowAuthority.ForeignWrite,LocationState.possible,Permission.isUnique]
  · have oldAt : tree.nodes.get index = some node :=
      (GeneralBorrowFreshLocation.get_other tree.nodes slot.index index _ fresh).symm.trans present
    have scalar := original index node oldAt
    exact ⟨fun below => scalar.1 (ancestry.mp below),fun outside => scalar.2 (fun below => outside (ancestry.mpr below))⟩

private theorem runtime_advanced (tree : BorrowTree) (global : GlobalState)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree (GeneralBorrowFnEntryRegistration.advanced global room) := by
  refine ⟨runtime.formed,runtime.coherent,runtime.possible,?_⟩
  apply GeneralBorrowForestTagHighWaterHistory.weaken tree global.protectedTags global.nextPointerTag
    (TypedRetagEmpty.successorTag global.nextPointerTag room) runtime.below
  have next := GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
  omega

private theorem original_runtime_after_effect {options before tracker argument}
    (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree (CurrentCallEmptyEntryArguments.nextTracker effect fresh).global := by
  cases effect with
  | integer => exact runtime_advanced tree tracker.global fresh runtime
  | miss => exact runtime_advanced tree tracker.global fresh runtime
  | concreteLive address id parent entry childTree live child =>
    exact (GeneralBorrowFnEntryRegistrationRuntime.prepare tree tracker.global {} id fresh runtime).2.2.2.1
  | concreteNonlive address id parent metadata absent =>
    exact (GeneralBorrowFnEntryRegistrationRuntime.prepare tree tracker.global {} id fresh runtime).2.2.2.1
  | concreteImage address id parent image source converted descriptor attributes =>
    exact (GeneralBorrowFnEntryRegistrationRuntime.prepare tree tracker.global {} id fresh runtime).2.2.2.1
  | wildcardLive address hit entry childTree live child =>
    exact (GeneralBorrowFnEntryRegistrationRuntime.prepare tree tracker.global {} hit.id fresh runtime).2.2.2.1
  | wildcardNonlive address hit metadata absent =>
    exact (GeneralBorrowFnEntryRegistrationRuntime.prepare tree tracker.global {} hit.id fresh runtime).2.2.2.1
  | wildcardImage address hit image root source converted rootCached descriptor attributes =>
    exact (GeneralBorrowFnEntryRegistrationRuntime.prepare tree tracker.global {} hit.id fresh runtime).2.2.2.1


private theorem owned_registered (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (completion : Completion) (source : UniIndex) (lower upper : UInt64)
    (owned : OwnedOn (Authority tree completion global.protectedTags source) lower upper tree.locations) :
    OwnedOn (Authority tree completion (GeneralBorrowFnEntryRegistration.registered global frame allocation room).1.protectedTags source)
      lower upper tree.locations := by
  obtain ⟨_,_,_,_,nodeFresh,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation room runtime
  intro cursor valid positive start stop index node present
  have flags := ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag node.tag .StrongProtector
    (nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))
  have registeredFlags : (GeneralBorrowFnEntryRegistration.registered global frame allocation room).1.protectedTags.contains node.tag = global.protectedTags.contains node.tag := flags
  change (Below completion index source → OrdinaryBorrowAuthority.LocalWrite _ _) ∧ (¬Below completion index source → OrdinaryBorrowAuthority.ForeignWrite _ _)
  rw [registeredFlags]
  exact owned cursor valid positive start stop index node present

private theorem original_owned_after_effect {options before tracker argument}
    (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (completion : Completion) (source : UniIndex) (lower upper : UInt64)
    (owned : OwnedOn (Authority tree completion tracker.global.protectedTags source) lower upper tree.locations) :
    OwnedOn (Authority tree completion (CurrentCallEmptyEntryArguments.nextTracker effect fresh).global.protectedTags source)
      lower upper tree.locations := by
  cases effect with
  | integer | miss => exact owned
  | concreteLive address id parent entry childTree live child =>
    exact owned_registered tree tracker.global {} id fresh runtime completion source lower upper owned
  | concreteNonlive address id parent metadata absent =>
    exact owned_registered tree tracker.global {} id fresh runtime completion source lower upper owned
  | concreteImage address id parent image data converted descriptor attributes =>
    exact owned_registered tree tracker.global {} id fresh runtime completion source lower upper owned
  | wildcardLive address hit entry childTree live child =>
    exact owned_registered tree tracker.global {} hit.id fresh runtime completion source lower upper owned
  | wildcardNonlive address hit metadata absent =>
    exact owned_registered tree tracker.global {} hit.id fresh runtime completion source lower upper owned
  | wildcardImage address hit image root sourceImage converted rootCached descriptor attributes =>
    exact owned_registered tree tracker.global {} hit.id fresh runtime completion source lower upper owned


private theorem effect_counter {options before tracker argument} (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) :
    (CurrentCallEmptyEntryArguments.nextTracker effect fresh).global.nextPointerTag = TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh := by
  cases effect <;> rfl

private theorem effect_tag_room {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    (CurrentCallEmptyEntryArguments.nextTracker effect fresh).global.nextPointerTag.value < 18446744073709551615 := by
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  have original := input.machine.resources.tagRoom
  have next := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
  change (CurrentCallEmptyEntryArguments.nextTracker effect fresh).global.nextPointerTag.value < 18446744073709551615
  rw [effect_counter effect fresh]
  apply UInt64.lt_iff_toNat_lt.mpr
  change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat < 18446744073709551615
  omega

private theorem zero_slot_order (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (complete : Completes tree completion) (order : ParentTagOrder tree) : ParentTagOrder (slot.after tag) := by
  intro child childNode childAt parent parentNode edge parentAt
  by_cases fresh : child = slot.index
  · subst child
    have nodeEq : childNode = WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None :=
      Option.some.inj (childAt.symm.trans (GeneralBorrowFreshLocation.get_same _ _ _))
    subst childNode
    cases edge
  · have oldChild : tree.nodes.get child = some childNode :=
      (GeneralBorrowFreshLocation.get_other tree.nodes slot.index child _ fresh).symm.trans childAt
    have completedEdge := (complete.2.2.2.2.1 child childNode oldChild).2.2.1 parent edge
    obtain ⟨oldParent,oldParentAt⟩ := (complete.2.2.2.2.2.2 child parent completedEdge).2.1
    have parentDifferent : parent ≠ slot.index := by intro same;rw [same,slot.vacant] at oldParentAt;cases oldParentAt
    change (tree.nodes.insert slot.index _).get parent = some parentNode at parentAt
    rw [GeneralBorrowFreshLocation.get_other _ slot.index parent _ parentDifferent] at parentAt
    exact order child childNode oldChild parent parentNode edge parentAt

private theorem zero_slot_distinct (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (complete : Completes tree completion) : (slot.after tag).roots.toList.Nodup := by
  change (tree.roots.push slot.index).toList.Nodup
  rw [Array.toList_push]
  apply List.nodup_append.mpr
  refine ⟨complete.2.2.1,by simp,?_⟩
  intro old member query single
  have equal : query = slot.index := by simpa only [List.mem_singleton] using single
  subst query
  intro same
  subst old
  obtain ⟨position,rootAt⟩ := Array.getElem?_of_mem (Array.mem_toList_iff.mp member)
  obtain ⟨node,nodeAt,_⟩ := complete.2.2.2.1 position slot.index rootAt
  rw [slot.vacant] at nodeAt
  cases nodeAt

private theorem zero_physical_runtime (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    tree.tagMapping.get node.tag = some index ∧
    (∀ child, child ∈ node.children.toList ↔
      ∃ childNode, tree.nodes.get child = some childNode ∧ childNode.parent = some index) ∧
    (node.parent = none ↔ index ∈ tree.roots.toList) := by
  obtain ⟨forest⟩ := runtime.formed.forest default global.protectedTags
  obtain ⟨depth⟩ := runtime.formed.depth
  have reciprocal := GeneralBorrowExposedScopedReciprocal.of_forest tree default global.protectedTags forest depth
  refine ⟨runtime.formed.allocator.nodeTags index node present,?_,?_⟩
  · intro child
    constructor
    · intro member
      obtain ⟨childNode,childAt⟩ := runtime.formed.children index node present child member
      let topology := (source_normal_projection tree default global.protectedTags).topology
      have size : topology.nodes.size = tree.nodes.data.size := by
        unfold topology
        unfold_general_projection
        unfold_general_topology
        simp only [Array.size_map]
      have indexValid : index.toNat < topology.nodes.size := by
        rw [size]; exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ present
      have childValid : child.toNat < topology.nodes.size := by
        rw [size]; exact GeneralBorrowNodeUpdate.lookup_valid _ _ _ childAt
      have parentProjection := GeneralBorrowProjection.projection_topology_node tree default global.protectedTags index.toNat index node rfl present
      have childProjection := GeneralBorrowProjection.projection_topology_node tree default global.protectedTags child.toNat child childNode rfl childAt
      change (topology.nodes[index.toNat]?.getD ⟨none,[]⟩) = _ at parentProjection
      change (topology.nodes[child.toNat]?.getD ⟨none,[]⟩) = _ at childProjection
      simp only [Array.getElem?_eq_getElem indexValid,Option.getD_some] at parentProjection
      simp only [Array.getElem?_eq_getElem childValid,Option.getD_some] at childProjection
      have projectedMember : child.toNat ∈ (topology.nodes[index.toNat]'indexValid).children := by
        rw [parentProjection]
        exact List.mem_map.mpr ⟨child,member,rfl⟩
      obtain ⟨valid,edge⟩ := forest.childParent index.toNat indexValid child.toNat projectedMember
      rw [childProjection] at edge
      have parentEq : childNode.parent = some index := by
        cases h : childNode.parent with
        | none => simp [h] at edge
        | some actual =>
          simp only [h,Option.map_some] at edge
          have same : actual = index := GeneralBorrowNodeUpdate.index_injective _ _ (Option.some.inj edge)
          exact congrArg some same
      exact ⟨childNode,childAt,parentEq⟩
    · rintro ⟨childNode,childAt,edge⟩
      obtain ⟨parentNode,parentAt,member⟩ := reciprocal child childNode childAt index edge
      have same : parentNode = node := Option.some.inj (parentAt.symm.trans present)
      simpa only [same] using member
  · constructor
    · exact runtime.formed.covered index node present
    · intro member
      obtain ⟨rootNode,rootAt,parentless⟩ := runtime.formed.rootNodes index member
      have same : node = rootNode := Option.some.inj (present.symm.trans rootAt)
      simpa only [same] using parentless


private theorem zero_completes_of_exposed_return (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (global : GlobalState) (complete : Completes tree completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts (slot.after tag) global)
    (origin : UniIndex) (originNode : TreeNode) (originAt : tree.nodes.get origin = some originNode)
    (exposed : originNode.isExposed = true) (older : originNode.tag.value < tag.value)
    (position : Nat) (root : UniIndex) (rootAt : tree.roots[position]? = some root)
    (path : GeneralBorrowExposedNonleafPrimaryPath.Path tree root origin) :
    Completes (slot.after tag) (S05ConcreteProtectedChildCompletion.extend completion slot.index origin) := by
  have frame : S05WildcardProtectedRootCompletion.RootFrame tree (slot.after tag) slot.index origin tag := by
    refine ⟨slot.vacant,?_,rfl,⟨originNode,originAt⟩,⟨_,GeneralBorrowFreshLocation.get_same _ _ _,rfl,rfl⟩,?_,?_,
      zero_physical_runtime (slot.after tag) global runtime⟩
    · change (tree.nodes.insert slot.index _).data.size = max tree.nodes.data.size (slot.index.toNat+1)
      simp only [UniValMap.insert,Id.run,pure]
      split <;> simp only [Array.size_set,UniValMap.extendTo,Array.size_append,Array.size_replicate] <;> omega
    · intro index node present
      have different : index ≠ slot.index := by
        intro same
        rw [same,slot.vacant] at present
        cases present
      exact ⟨node,(GeneralBorrowFreshLocation.get_other _ _ _ _ different).trans present,rfl,rfl,rfl⟩
    · intro index node present
      by_cases same : index = slot.index
      · exact Or.inl same
      · exact Or.inr ⟨node,(GeneralBorrowFreshLocation.get_other _ _ _ _ same).symm.trans present,rfl⟩
  exact S05WildcardProtectedRootCompletion.completes_of_root tree (slot.after tag) completion complete slot.index origin tag frame
    originNode originAt exposed older position root rootAt path

private def zeroAbsentDefault : LocationState := ⟨.Disabled,false,.None⟩

private theorem zero_projection_slot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (position : Nat) (query : UniIndex) (converted : UniIndex.ofNat? position = some query)
    (equal : query.toNat = position) (valid : position < tree.nodes.data.size) :
    (source_normal_projection tree location protections).stateAt position =
      some ((location.perms.get query).getD (((tree.nodeAt query).map TreeNode.defaultLocationState).getD zeroAbsentDefault)) := by
  have nodeValue : tree.nodeAt query = tree.nodes.data[position]'valid := by
    unfold BorrowTree.nodeAt UniValMap.get
    simp only [equal,Array.getElem?_eq_getElem valid]
  unfold_general_projection
  unfold NormalTreeState.stateAt
  simp only [Array.getElem?_mapIdx,Array.getElem?_map,Array.getElem?_eq_getElem valid,
    converted,Option.map_some]
  rw [nodeValue]
  generalize stateEq : location.perms.get query = stored
  clear stateEq
  generalize nodeEq : tree.nodes.data[position] = node
  clear nodeEq
  cases stored <;> cases node <;> rfl

private theorem zero_protected_old (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (location : LocationTree) (protections : ProtectedTags) (query : UniIndex) (different : query ≠ slot.index) :
    (source_normal_projection (slot.after tag) location protections).protectedNodes.contains query.toNat =
      (source_normal_projection tree location protections).protectedNodes.contains query.toNat := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem,GeneralBorrowFreshReuseProtection.protected_iff]
  have lookup : (slot.after tag).nodeAt query = tree.nodeAt query :=
    GeneralBorrowFreshLocation.get_other tree.nodes slot.index query _ different
  rw [lookup]

private theorem zero_normal_of_foreign (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (location : LocationTree) (protections : ProtectedTags)
    (fits : tree.nodes.size ≤ 4294967296)
    (foreign : OrdinaryBorrowAuthority.ForeignWrite
      ((location.perms.get slot.index).getD (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None).defaultLocationState)
      (protections.contains tag))
    (observer : UniIndex) (node : TreeNode) (present : tree.nodeAt observer = some node)
    (old : DuplicatePrefixBorrowAuthorization.Normal tree location protections observer) :
    ∃ next : DuplicatePrefixBorrowAuthorization.Normal (slot.after tag) location protections observer,
      next.component.support = old.component.support := by
  let component : GeneralBorrowExposedScopedNormal.Component
      (source_normal_projection (slot.after tag) default protections).topology observer.toNat := {
    support := old.component.support
    anchor := old.component.anchor
    parents := by
      intro current included parent edge
      rw [S04ZeroRootObserverNormal.topology_node] at edge
      exact old.component.parents current included parent edge
    children := by
      intro current included child member
      rw [S04ZeroRootObserverNormal.topology_node] at member
      exact old.component.children current included child member }
  refine ⟨⟨component,?_⟩,rfl⟩
  intro kind position included bound
  by_cases fresh : position = slot.index.toNat
  · subst position
    let newNode := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
    have newAt : (slot.after tag).nodes.get slot.index = some newNode := GeneralBorrowFreshLocation.get_same _ _ _
    refine ⟨(location.perms.get slot.index).getD newNode.defaultLocationState,?_,?_⟩
    · rw [projection_location_state (slot.after tag) location protections slot.index newNode newAt]
      simp only [BorrowTree.locationStateAt,show (slot.after tag).nodeAt slot.index = some newNode from newAt]
      rfl
    · rw [S04ZeroRootObserverNormal.foreign_new tree slot tag depth location protections observer node present,
        GeneralBorrowNormalPermissionMetadata.held (slot.after tag) location protections slot.index newNode newAt]
      cases kind with
      | Write => exact foreign
      | Read => exact S05CompletedAncestryReadQueries.foreign_read _ _ foreign
  · have oldBound := S04ZeroRootObserverNormal.old_bound tree slot tag position bound fresh
    obtain ⟨query,converted,equal⟩ := index_nat position (by omega)
    have different : query ≠ slot.index := by
      intro same
      exact fresh (equal.symm.trans (congrArg UniIndex.toNat same))
    obtain ⟨state,lookup,compatible⟩ := old.permissions kind position included oldBound
    have oldState : (source_normal_projection (slot.after tag) location protections).stateAt position =
        (source_normal_projection tree location protections).stateAt position := by
      rw [zero_projection_slot _ _ _ position query converted equal bound,
        zero_projection_slot _ _ _ position query converted equal oldBound]
      have lookup : (slot.after tag).nodeAt query = tree.nodeAt query :=
        GeneralBorrowFreshLocation.get_other tree.nodes slot.index query _ different
      rw [lookup]
    refine ⟨state,oldState.trans lookup,?_⟩
    have held := zero_protected_old tree slot tag location protections query different
    rw [equal] at held
    rw [held]
    unfold GeneralBorrowAnchor.relation
    rw [S04ZeroRootObserverNormal.old_path tree slot tag depth location protections observer node present]
    exact compatible

private theorem zero_raw_of_normal (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (location : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (nextFormed : GeneralBorrowStructuralHistoryState.GraphState (slot.after tag))
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (fits : tree.nodes.data.size ≤ 4294967296)
    (position : Nat) (root source : UniIndex) (rootNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root source)
    (normal : DuplicatePrefixBorrowAuthorization.Normal (slot.after tag) location protections source) :
    ∀ index node, tree.nodes.get index = some node → GeneralBorrowExposedNonleafPrimaryPath.Path tree root index →
      (Below completion index source → OrdinaryBorrowAuthority.LocalWrite
        ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
      (¬Below completion index source → OrdinaryBorrowAuthority.ForeignWrite
        ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) := by
  obtain ⟨actual,found,parentless⟩ := complete.2.2.2.1 position root rootSlot
  have same : actual = rootNode := Option.some.inj (found.symm.trans rootPresent)
  subst actual
  obtain ⟨forest⟩ := formed.forest location protections
  obtain ⟨nextForest⟩ := nextFormed.forest location protections
  obtain ⟨sourceNode,sourcePresent⟩ := sourcePath.present
  have extend (query : UniIndex) (path : GeneralBorrowExposedNonleafPrimaryPath.Path tree root query) :
      GeneralBorrowExposedNonleafPrimaryPath.Path (slot.after tag) root query := by
    apply GeneralBorrowSharedAuthorizationGeometry.path_extension tree (slot.after tag) _ root query path
    intro index node present
    exact ⟨node,S04ZeroRootObserverNormal.old_node tree slot tag index node present,rfl⟩
  have projectedSource := GeneralBorrowPhysicalRootPath.projection_desc (slot.after tag) location protections root source (extend source sourcePath)
  have rootInside := GeneralBorrowNormalComponentNormalization.contains_ancestor _ source.toNat normal.component
    root.toNat source.toNat projectedSource normal.component.anchor
  intro index node present path
  have nextPresent := S04ZeroRootObserverNormal.old_node tree slot tag index node present
  have projected := GeneralBorrowPhysicalRootPath.projection_desc (slot.after tag) location protections root index (extend index path)
  have supported := GeneralBorrowNormalComponentNormalization.contains_descendant _ nextForest source.toNat normal.component
    root.toNat index.toNat projected rootInside
  obtain ⟨state,stored,compatible⟩ := normal.permissions .Write index.toNat supported
    (GeneralBorrowNodeUpdate.lookup_valid (slot.after tag).nodes index node nextPresent)
  have actualState := GeneralBorrowProjection.projection_state (slot.after tag) location protections index.toNat index node
    (GeneralBorrowProjection.index_self index) rfl nextPresent
  have equal : state = ((location.perms.get index).getD node.defaultLocationState) := Option.some.inj (stored.symm.trans actualState)
  subst state
  rw [GeneralBorrowNormalPermissionMetadata.held (slot.after tag) location protections index node nextPresent] at compatible
  have physical := CompletedBorrowPhysicalSource.same_root_ancestor_iff complete rootPresent parentless present path sourcePath
  have related := GeneralBorrowProjectedDescPath.relation_local_iff tree location protections fits depth forest
    source index sourceNode node sourcePresent present
  have sameRelation : GeneralBorrowAnchor.relation (source_normal_projection (slot.after tag) location protections) source.toNat index.toNat =
      GeneralBorrowAnchor.relation (source_normal_projection tree location protections) source.toNat index.toNat := by
    unfold GeneralBorrowAnchor.relation
    rw [S04ZeroRootObserverNormal.old_path tree slot tag depth location protections source sourceNode sourcePresent]
  rw [sameRelation] at compatible
  constructor
  · intro below
    rw [related.mpr (physical.mp below)] at compatible
    exact compatible
  · intro outside
    have relation : GeneralBorrowAnchor.relation (source_normal_projection tree location protections) source.toNat index.toNat = .ForeignAccess := by
      cases current : GeneralBorrowAnchor.relation (source_normal_projection tree location protections) source.toNat index.toNat with
      | LocalAccess => exact False.elim (outside (physical.mpr (related.mp current)))
      | ForeignAccess => rfl
    rw [relation] at compatible
    exact compatible

private def ZeroRights (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (protections : ProtectedTags) (source : UniIndex) (location : LocationTree) : Prop :=
  (∀ index node, tree.nodes.get index = some node →
    (Below completion index source → OrdinaryBorrowAuthority.LocalWrite
      ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) ∧
    (¬Below completion index source → OrdinaryBorrowAuthority.ForeignWrite
      ((location.perms.get index).getD node.defaultLocationState) (protections.contains node.tag))) ∧
  OrdinaryBorrowAuthority.ForeignWrite
    ((location.perms.get slot.index).getD (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None).defaultLocationState)
    (protections.contains tag)


private theorem zero_normal_read (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (location : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (nextFormed : GeneralBorrowStructuralHistoryState.GraphState (slot.after tag))
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (position : Nat) (root source : UniIndex) (rootNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root source)
    (clean : location.perms.get slot.index = none)
    (rights : ZeroRights tree slot tag completion protections source location)
    (coherent : LocationCoherent (slot.after tag) location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) location)
    (short : (slot.after tag).nodes.size < 65536) (mode : ChildrenVisitMode) :
    let result := (slot.after tag).performNormalAccessAt location source .Read protections mode
    result.access.status = .Completed ∧ result.outcome = .ok () ∧
      LocationCoherent (slot.after tag) result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) result.location ∧
      ZeroRights tree slot tag completion protections source result.location := by
  have fits : tree.nodes.data.size ≤ 4294967296 := by
    have growth := slot.size tag
    rw [growth] at short
    change tree.nodes.data.size+slot.growth < 65536 at short
    omega
  have nextFits : (slot.after tag).nodes.data.size ≤ 4294967296 := by
    change (slot.after tag).nodes.data.size < 65536 at short
    omega
  obtain ⟨oldNormal⟩ := S05CompletedAncestryNormal.normal tree completion location protections complete formed depth fits
    position root source rootNode rootSlot rootPresent sourcePath
    (fun index node present _ => (rights.1 index node present).1)
    (fun index node present _ => (rights.1 index node present).2)
  obtain ⟨sourceNode,sourcePresent⟩ := sourcePath.present
  obtain ⟨normal,_⟩ := S04ZeroRootObserverNormal.normal tree slot tag depth location protections fits clean source sourceNode sourcePresent oldNormal
  have nextPresent := S04ZeroRootObserverNormal.old_node tree slot tag source sourceNode sourcePresent
  have done := GeneralBorrowReadCapabilityNormal.access (slot.after tag) location protections nextFormed source sourceNode nextPresent
    (DuplicatePrefixNormalKind.of_normal (slot.after tag) location protections source normal .Read) coherent profile possible short mode
  obtain ⟨forest⟩ := formed.forest location protections
  obtain ⟨nextForest⟩ := nextFormed.forest location protections
  obtain ⟨nextNormal,_⟩ := DuplicatePrefixNormalAuthorizationPreservation.normal_preserves_component
    (slot.after tag) location protections source .Read mode nextFits nextForest
    (GeneralBorrowExposedScopedNormalMetadata.valid_aligned (slot.after tag) location protections source sourceNode nextPresent).1 normal
  have selectedRights := zero_raw_of_normal tree slot tag completion _ protections complete formed nextFormed depth fits
    position root source rootNode rootSlot rootPresent sourcePath nextNormal
  obtain ⟨actual,actualAt,parentless⟩ := complete.2.2.2.1 position root rootSlot
  have actualEq : actual = rootNode := Option.some.inj (actualAt.symm.trans rootPresent)
  subst actual
  have extend (other query : UniIndex) (path : GeneralBorrowExposedNonleafPrimaryPath.Path tree other query) :
      GeneralBorrowExposedNonleafPrimaryPath.Path (slot.after tag) other query := by
    apply GeneralBorrowSharedAuthorizationGeometry.path_extension tree (slot.after tag) _ other query path
    intro index node present
    exact ⟨node,S04ZeroRootObserverNormal.old_node tree slot tag index node present,rfl⟩
  have rootPath := S05CompletedAncestryNormal.root_path (slot.after tag) location protections nextFormed root source rootNode
    (S04ZeroRootObserverNormal.old_node tree slot tag root rootNode rootPresent) parentless (extend root source sourcePath)
  have frame (other : UniIndex) (member : other ∈ (slot.after tag).roots.toList) (different : root ≠ other) :=
    (GeneralBorrowNormalOtherRootFrame.access_kind (slot.after tag) location protections nextFormed source root other sourceNode nextPresent
      .Read (DuplicatePrefixNormalKind.of_normal (slot.after tag) location protections source normal .Read) rootPath member different coherent mode).2.2.2
  refine ⟨done.1,done.2.1,done.2.2.1,done.2.2.2.1,done.2.2.2.2.1,?_,?_⟩
  · intro index node present
    have projectedSelf := GeneralBorrowPhysicalRootPath.projection_desc tree location protections index index (.refl _ node present)
    obtain ⟨other,otherNode,otherAt,otherParentless,member,last⟩ := GeneralBorrowRootMembership.terminal
      tree location protections forest depth formed.covered index node present projectedSelf.valid.1
    let topology := (source_normal_projection tree location protections).topology
    have nonempty : topology.ancestorPath index.toNat ≠ [] :=
      GeneralBorrowTerminal.ancestors_nonempty topology topology.nodes.size index.toNat
    have ending : (topology.ancestorPath index.toNat).getLast? = some other.toNat := by
      have lastValue : (topology.ancestorPath index.toNat).getLast! = (topology.ancestorPath index.toNat).getLast nonempty := by
        rw [List.getLast!_eq_getLast?_getD,List.getLast?_eq_some_getLast nonempty];rfl
      rw [lastValue] at last
      rw [List.getLast?_eq_some_getLast nonempty,last]
    have projectedPath := GeneralBorrowPhysicalRootPath.selected_desc topology forest index.toNat other.toNat projectedSelf.valid.1 ending
    obtain ⟨actual,actualNode,actualIndex,actualAt,path⟩ := GeneralBorrowProjectedDescPath.desc_path
      tree location protections fits other otherNode otherAt index.toNat projectedPath
    have actualEq : actual = index := by
      cases actual;cases index
      simp only [UniIndex.toNat] at actualIndex
      congr
      exact UInt32.toNat_inj.mp actualIndex
    subst actual
    by_cases same : other = root
    · subst other
      exact selectedRights index node present path
    · have nextMember : other ∈ (slot.after tag).roots.toList := by
        change other ∈ (tree.roots.push slot.index).toList
        simp only [Array.toList_push,List.mem_append,List.mem_singleton]
        exact Or.inl member
      rw [frame other nextMember (Ne.symm same) index node
        (S04ZeroRootObserverNormal.old_node tree slot tag index node present) (extend other index path)]
      exact rights.1 index node present
  · have different : root ≠ slot.index := by
      intro same
      rw [same,slot.vacant] at rootPresent
      cases rootPresent
    have member : slot.index ∈ (slot.after tag).roots.toList := by
      change slot.index ∈ (tree.roots.push slot.index).toList
      simp only [Array.toList_push,List.mem_append,List.mem_singleton]
      exact Or.inr trivial
    rw [frame slot.index member different slot.index _ (GeneralBorrowFreshLocation.get_same _ _ _)
      (.refl slot.index _ (GeneralBorrowFreshLocation.get_same _ _ _))]
    exact rights.2

/-- Internal finite-effect consumer: the actual Read root scan preserves the
original Bool-relative rights and the real dormant-root ForeignWrite right. -/
private theorem zero_read_roots (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (current : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (oldOrder : ParentTagOrder tree) (selectedPosition : Nat) (selectedRoot source : UniIndex) (selectedNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selectedRoot)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (selectedPath : GeneralBorrowExposedNonleafPrimaryPath.Path tree selectedRoot source)
    (formed : GeneralBorrowStructuralHistoryState.GraphState (slot.after tag))
    (distinct : (slot.after tag).roots.toList.Nodup) (order : ParentTagOrder (slot.after tag))
    (coherent : LocationCoherent (slot.after tag) current protections) (short : (slot.after tag).nodes.size < 65536)
    (profile : GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) current protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) current)
    (rights : ZeroRights tree slot tag completion protections source current)
    (minimum : Option BorTag) (mode : ChildrenVisitMode) (range : ByteRange) :
    let final := (forIn (List.range' 0 (slot.after tag).roots.size) (current,none,false)
      (GeneralBorrowConcreteRowCutoffAccess.scan (slot.after tag) selectedRoot (some selectedNode.tag) minimum .Read protections mode range) : Id GeneralBorrowConcreteRowCutoffAccess.State)
    final.2.1 = none ∧ LocationCoherent (slot.after tag) final.1 protections ∧
      GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) final.1 protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) final.1 ∧
      (∀ index node, (slot.after tag).nodes.get index = some node →
        GeneralBorrowExposedNonleafPrimaryPath.Path (slot.after tag) selectedRoot index →
        final.1.perms.get index = current.perms.get index) ∧
      ZeroRights tree slot tag completion protections source final.1 := by
  have selectedBound := (Array.getElem?_eq_some_iff.mp selectedSlot).1
  have selectedNext : (slot.after tag).roots[selectedPosition]? = some selectedRoot := by
    change (tree.roots.push slot.index)[selectedPosition]? = some selectedRoot
    simpa only [Array.getElem?_push,ite_eq_right (Nat.ne_of_lt selectedBound)] using selectedSlot
  have nonempty : 0 < tree.roots.size := by omega
  have extend (root query : UniIndex) (path : GeneralBorrowExposedNonleafPrimaryPath.Path tree root query) :
      GeneralBorrowExposedNonleafPrimaryPath.Path (slot.after tag) root query := by
    apply GeneralBorrowSharedAuthorizationGeometry.path_extension tree (slot.after tag) _ root query path
    intro index node present
    exact ⟨node,S04ZeroRootObserverNormal.old_node tree slot tag index node present,rfl⟩
  apply CurrentCallEmptyEntryRootLoop.roots (slot.after tag) current protections formed distinct selectedPosition selectedRoot selectedNext
    (ZeroRights tree slot tag completion protections source) (some selectedNode.tag) .Read
  · intro position root rootAt different location retained cache sifa gp _
    change (tree.roots.push slot.index)[position]? = some root at rootAt
    by_cases oldPosition : position < tree.roots.size
    · have oldSlot : tree.roots[position]? = some root := by
        simpa only [Array.getElem?_push,ite_eq_right (Nat.ne_of_lt oldPosition)] using rootAt
      obtain ⟨done,outCache,outProfile,outPossible,outside,localRight,foreignRight⟩ :=
        CurrentCallEmptyEntryZeroRootQueries.old_read_access tree slot tag completion location protections complete depth oldOrder
          position selectedPosition root selectedRoot source selectedNode oldSlot selectedSlot selectedPresent different selectedPath
          (fun index node present _ below => (retained.1 index node present).1 below)
          (fun index node present _ below => (retained.1 index node present).2 below)
          formed order cache short sifa gp
      refine ⟨done,outCache,outProfile,outPossible,?_,?_,?_⟩
      · intro query notPath
        exact outside query (fun oldPath => notPath (extend root query oldPath))
      · intro index node present
        by_cases path : GeneralBorrowExposedNonleafPrimaryPath.Path tree root index
        · exact ⟨localRight index node present path,foreignRight index node present path⟩
        · rw [outside index path]
          exact retained.1 index node present
      · have notPath : ¬GeneralBorrowExposedNonleafPrimaryPath.Path tree root slot.index := by
          intro path
          obtain ⟨node,present⟩ := path.present
          rw [slot.vacant] at present
          cases present
        rw [outside slot.index notPath]
        exact retained.2
    · have indexPosition : position = tree.roots.size := by
        by_cases equal : position = tree.roots.size
        · exact equal
        · simp only [Array.getElem?_push,ite_eq_right equal] at rootAt
          have missing : tree.roots[position]? = none := Array.getElem?_eq_none (by omega)
          rw [missing] at rootAt
          cases rootAt
      subst position
      have rootEq : slot.index = root := by
        simpa only [Array.getElem?_push,↓reduceIte,Option.some.injEq] using rootAt
      subst root
      obtain ⟨done,outCache,outProfile,outPossible,outside,newForeign⟩ :=
        CurrentCallEmptyEntryZeroRootQueries.new_read_access tree slot tag depth location protections nonempty
          (some selectedNode.tag) retained.2 formed order cache short sifa gp
      refine ⟨done,outCache,outProfile,outPossible,?_,?_,newForeign⟩
      · intro query notPath
        apply outside query
        intro same
        subst query
        exact notPath (.refl slot.index _ (GeneralBorrowFreshLocation.get_same _ _ _))
      · intro index node present
        have different : index ≠ slot.index := by
          intro same
          rw [same,slot.vacant] at present
          cases present
        rw [outside index different]
        exact retained.1 index node present
  · exact rights
  · exact coherent
  · exact profile
  · exact possible
  · intros;rfl



private theorem zero_lookup_shape (first second : LocationTree) (same : locationShape second = locationShape first)
    (index : UniIndex) : (second.perms.get index).map stateShape = (first.perms.get index).map stateShape := by
  have cell := congrArg (fun rows => rows[index.toNat]?) same
  simp only [locationShape,Array.getElem?_map] at cell
  have flat := congrArg (fun value : Option (Option StateShape) => value.getD none) cell
  unfold UniValMap.get
  cases firstAt : first.perms.data[index.toNat]? <;> cases secondAt : second.perms.data[index.toNat]? <;> simp_all

private theorem zero_effective_shape (first second : LocationTree) (old next : TreeNode)
    (same : locationShape second = locationShape first)
    (permission : next.defaultInitialPermission = old.defaultInitialPermission) (index : UniIndex) :
    stateShape (RawState second index next) = stateShape (RawState first index old) := by
  have cell := zero_lookup_shape first second same index
  unfold RawState
  cases oldAt : first.perms.get index <;> cases nextAt : second.perms.get index <;>
    simp_all [stateShape,TreeNode.defaultLocationState]

private theorem zero_authority_state (old next : LocationState) (same : stateShape next = stateShape old)
    (held : Bool) :
    (LocalWrite next held ↔ LocalWrite old held) ∧ (ForeignWrite next held ↔ ForeignWrite old held) := by
  have permission := congrArg Prod.fst same
  have accessed := congrArg Prod.snd same
  simp only [stateShape] at permission accessed
  simp [LocalWrite,ForeignWrite,LocationState.possible,permission,accessed]

private theorem zero_rights_shape (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (protections : ProtectedTags) (source : UniIndex) (first second : LocationTree)
    (same : GeneralBorrowView.locationShape second = GeneralBorrowView.locationShape first)
    (rights : ZeroRights tree slot tag completion protections source first) :
    ZeroRights tree slot tag completion protections source second := by
  refine ⟨?_,?_⟩
  · intro index node present
    have scalar := zero_authority_state _ _ (zero_effective_shape first second node node same rfl index) (protections.contains node.tag)
    exact ⟨fun below => scalar.1.mpr ((rights.1 index node present).1 below),fun below => scalar.2.mpr ((rights.1 index node present).2 below)⟩
  · let node := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
    have scalar := zero_authority_state _ _ (zero_effective_shape first second node node same rfl slot.index) (protections.contains tag)
    exact scalar.2.mpr rights.2

private theorem zero_rights_materialized (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (protections : ProtectedTags) (source child : UniIndex)
    (vacant : (slot.after tag).nodes.get child = none) (location : LocationTree)
    (rights : ZeroRights tree slot tag completion protections source location) :
    ZeroRights tree slot tag completion protections source
      (GeneralBorrowFreshMaterialization.materialized location child GeneralBorrowFreshChild.inside) := by
  have different (index : UniIndex) (node : TreeNode) (present : (slot.after tag).nodes.get index = some node) : index ≠ child := by
    intro same
    rw [same,vacant] at present
    cases present
  refine ⟨?_,?_⟩
  · intro index node present
    have unequal := different index node (S04ZeroRootObserverNormal.old_node tree slot tag index node present)
    simpa only [GeneralBorrowFreshMaterialization.materialized,GeneralBorrowFreshLocation.get_other _ child index _ unequal] using rights.1 index node present
  · have unequal := different slot.index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) (GeneralBorrowFreshLocation.get_same _ _ _)
    simpa only [GeneralBorrowFreshMaterialization.materialized,GeneralBorrowFreshLocation.get_other _ child slot.index _ unequal] using rights.2

private theorem zero_rights_owned_shape (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (protections : ProtectedTags) (source : UniIndex) (before after : BorrowTree)
    (lower upper : UInt64) (same : GeneralBorrowView.treeShape after = GeneralBorrowView.treeShape before)
    (owned : OwnedOn (ZeroRights tree slot tag completion protections source) lower upper before.locations) :
    OwnedOn (ZeroRights tree slot tag completion protections source) lower upper after.locations := by
  have entries := congrArg (fun shape => shape.2.2.1) same
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    simpa only [GeneralBorrowView.treeShape,Array.size_map] using congrArg Array.size entries
  intro position valid positive lowerBound upperBound
  have oldValid : position < before.locations.entries.size := by omega
  have cell := congrArg (fun rows => rows[position]?) entries
  simp only [GeneralBorrowView.treeShape,Array.getElem?_map,Array.getElem?_eq_getElem valid,
    Array.getElem?_eq_getElem oldValid,Option.map_some,Option.some.injEq,Prod.mk.injEq] at cell
  have original := owned position oldValid positive (by simpa only [←cell.1] using lowerBound) (by simpa only [←cell.1] using upperBound)
  exact zero_rights_shape tree slot tag completion protections source _ _ cell.2 original


private theorem zero_rights_stage_owned (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (held : ProtectedTags) (source : UniIndex) (before stage : BorrowTree)
    (nodes : before.nodes = (slot.after tag).nodes) (child : UniIndex) (vacant : before.nodes.get child = none)
    (offset len : UInt64) (well : before.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ before.locations.size.bytes.toNat)
    (locations : stage.locations = (before.locations.modifyRange (Size.ofBytes offset) (Size.ofBytes len)
      (fun _ row => GeneralBorrowFreshMaterialization.materialized row child GeneralBorrowFreshChild.inside)).state)
    (owned : OwnedOn (ZeroRights tree slot tag completion held source) offset (offset+len) before.locations) :
    OwnedOn (ZeroRights tree slot tag completion held source) offset (offset+len) stage.locations := by
  rw [locations]
  apply GeneralBorrowSharedReadConstructor.materialize_owned before.locations (Size.ofBytes offset) (Size.ofBytes len) child GeneralBorrowFreshChild.inside
    (ZeroRights tree slot tag completion held source) (ZeroRights tree slot tag completion held source) well bounds owned
  intro row rights
  exact zero_rights_materialized tree slot tag completion held source child (nodes ▸ vacant) row rights

private theorem zero_rights_child_owned (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (held : ProtectedTags) (source : UniIndex) (before : BorrowTree) (global : GlobalState)
    (nodes : before.nodes = (slot.after tag).nodes)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts before global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : before.indexOfTag parentTag = some parent) (present : before.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh before.tagMapping newTag) (room : before.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ before.locations.size.bytes.toNat)
    (owned : OwnedOn (ZeroRights tree slot tag completion held source) offset (offset+len) before.locations) :
    OwnedOn (ZeroRights tree slot tag completion held source) offset (offset+len)
      (before.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
        (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree.locations := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth before runtime.formed.toState
  let nextSlot := GeneralBorrowStructuralHistoryMutable.slot before runtime.formed.toState parent parentNode present room
  cases nextSlot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨before,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have atEnd : (GeneralBorrowFreshMetadataChildMutable.index input).toNat = before.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
    have vacant : before.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have staged := zero_rights_stage_owned tree slot tag completion held source before (GeneralBorrowFreshMetadataChildMutable.stage input)
      nodes (GeneralBorrowFreshMetadataChildMutable.index input) vacant offset len runtime.formed.well bounds rfl owned
    exact zero_rights_owned_shape tree slot tag completion held source (GeneralBorrowFreshMetadataChildMutable.stage input)
      (GeneralBorrowFreshMetadataChildMutable.result input) offset (offset+len) (GeneralBorrowFreshMetadataChildMutable.shape input) staged
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨before,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have staged := zero_rights_stage_owned tree slot tag completion held source before (GeneralBorrowFreshMetadataChildMutableReuse.stage input)
      nodes index vacant offset len runtime.formed.well bounds rfl owned
    exact zero_rights_owned_shape tree slot tag completion held source (GeneralBorrowFreshMetadataChildMutableReuse.stage input)
      (GeneralBorrowFreshMetadataChildMutableReuse.result input) offset (offset+len) (GeneralBorrowFreshMetadataChildMutableReuse.shape input) staged

/-- The associated Read's actual row output supplies parent BOTH capabilities
for the real mutable Bool child constructor under the SAME final held table. -/
private theorem zero_parent_normal_owned (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (fits : tree.nodes.data.size ≤ 4294967296)
    (position : Nat) (root source : UniIndex) (rootNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root source)
    (locations : DedupRangeMap LocationTree) (lower upper : UInt64)
    (owned : OwnedOn (ZeroRights tree slot tag completion protections source) lower upper locations) :
    OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal
      {(slot.after tag) with locations := locations} location protections source)) lower upper locations := by
  intro position valid positive belowUpper aboveLower
  have rights := owned position valid positive belowUpper aboveLower
  obtain ⟨oldNormal⟩ := S05CompletedAncestryNormal.normal tree completion _ protections complete formed depth fits
    _ root source rootNode rootSlot rootPresent sourcePath
    (fun index node present _ => (rights.1 index node present).1)
    (fun index node present _ => (rights.1 index node present).2)
  obtain ⟨sourceNode,sourcePresent⟩ := sourcePath.present
  obtain ⟨next,_⟩ := zero_normal_of_foreign tree slot tag depth _ protections fits rights.2 source sourceNode sourcePresent oldNormal
  exact ⟨⟨next.component,next.permissions⟩⟩

set_option linter.unusedSimpArgs false in
/-- Actual full concrete Read after the exact empty wildcard effect. The
original completion governs old Bool rights; the dormant root remains foreign. -/
private theorem zero_concrete_read (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (location : LocationTree) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (nextFormed : GeneralBorrowStructuralHistoryState.GraphState (slot.after tag))
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (nextOrder : ParentTagOrder (slot.after tag)) (distinct : (slot.after tag).roots.toList.Nodup)
    (position : Nat) (root source : UniIndex) (rootNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root source)
    (clean : location.perms.get slot.index = none)
    (rights : ZeroRights tree slot tag completion protections source location)
    (coherent : LocationCoherent (slot.after tag) location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) location)
    (short : (slot.after tag).nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at (slot.after tag) location (some source) .Read protections mode range
    source_access_status result = none ∧
      LocationCoherent (slot.after tag) (source_access_location result) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) (source_access_location result) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) (source_access_location result) ∧
      ZeroRights tree slot tag completion protections source (source_access_location result) := by
  have normal := zero_normal_read tree slot tag completion location protections complete formed nextFormed depth position root source rootNode
    rootSlot rootPresent sourcePath clean rights coherent profile possible short mode
  have final := zero_read_roots tree slot tag completion
    ((slot.after tag).performNormalAccessAt location source .Read protections mode).location protections
    complete depth order position root source rootNode rootSlot rootPresent sourcePath nextFormed distinct nextOrder
    normal.2.2.1 short normal.2.2.2.1 normal.2.2.2.2.1 normal.2.2.2.2.2
    (if mode == .SkipChildrenOfAccessed then source_min_exposed (slot.after tag) source else none) mode range
  obtain ⟨actual,actualAt,parentless⟩ := complete.2.2.2.1 position root rootSlot
  have actualEq : actual = rootNode := Option.some.inj (actualAt.symm.trans rootPresent)
  subst actual
  have nextRoot := S04ZeroRootObserverNormal.old_node tree slot tag root rootNode rootPresent
  have nextPath : GeneralBorrowExposedNonleafPrimaryPath.Path (slot.after tag) root source := by
    apply GeneralBorrowSharedAuthorizationGeometry.path_extension tree (slot.after tag) _ root source sourcePath
    intro index node present
    exact ⟨node,S04ZeroRootObserverNormal.old_node tree slot tag index node present,rfl⟩
  have rootPath := S05CompletedAncestryNormal.root_path (slot.after tag) location protections nextFormed root source rootNode nextRoot parentless nextPath
  have ending : ((source_normal_projection (slot.after tag) location protections).topology.ancestorPath source.toNat).getLast! = root.toNat := by
    rw [List.getLast!_eq_getLast?_getD,rootPath];rfl
  have rootEq : ((slot.after tag).performNormalAccessAt location source .Read protections mode).access.root = root.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection (slot.after tag) location protections)).trans ending
  have nextRootLookup : (slot.after tag).nodes.get root = some rootNode := nextRoot
  dsimp only
  simp_tree_helpers
  simp only [normal.1,normal.2.1,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,nextRootLookup,Option.map_some,
    beq_self_eq_true,Bool.not_true,Bool.false_eq_true,↓reduceIte]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  simpa only [GeneralBorrowConcreteRowCutoffAccess.scan,Id.run,bind,pure] using
    (show _ from ⟨final.1,final.2.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2.2⟩)


private theorem zero_concrete_range (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (protections : ProtectedTags)
    (complete : Completes tree completion) (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (nextFormed : GeneralBorrowStructuralHistoryState.GraphState (slot.after tag))
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (nextOrder : ParentTagOrder (slot.after tag)) (distinct : (slot.after tag).roots.toList.Nodup)
    (position : Nat) (root source : UniIndex) (rootNode sourceNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root source)
    (mapped : (slot.after tag).indexOfTag sourceNode.tag = some source)
    (offset len : Size) (lower upper : UInt64)
    (owned : OwnedOn (fun location => location.perms.get slot.index = none ∧
      ZeroRights tree slot tag completion protections source location) lower upper (slot.after tag).locations)
    (well : (slot.after tag).locations.WellFormed)
    (runtime : GeneralRangeMapState.Every (fun location => LocationCoherent (slot.after tag) location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) location) (slot.after tag).locations)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ (slot.after tag).locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat) (requestUpper : (offset.bytes+len.bytes).toNat ≤ upper.toNat)
    (short : (slot.after tag).nodes.size < 65536) (mode : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract (slot.after tag)
      (ZeroRights tree slot tag completion protections source)
      (fun location => LocationCoherent (slot.after tag) location protections ∧
        GeneralBorrowLocationSifaConsistency.Profile (slot.after tag) location protections ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible (slot.after tag) location)
      (fun _ _ => True) lower upper
      ((slot.after tag).performBorrowAccessRange (.concrete sourceNode.tag) offset len .Read protections mode) := by
  apply GeneralBorrowConcreteRangeEntry.access (slot.after tag) protections sourceNode.tag source mapped offset len .Read mode
    _ _ _ _ (fun _ authority => authority.2) (fun _ => trivial) _ lower upper owned well runtime bounds requestLower requestUpper
  intro location authority representation range
  have row := zero_concrete_read tree slot tag completion location protections complete formed nextFormed depth order nextOrder distinct
    position root source rootNode rootSlot rootPresent sourcePath authority.1 authority.2 representation.1 representation.2.1 representation.2.2 short mode range
  exact ⟨row.1,row.2.2.2.2,⟨row.2.1,row.2.2.1,row.2.2.2.1⟩,trivial⟩



private theorem mutable_shape_modify (map : DedupRangeMap LocationTree) (child parent : UniIndex) (tag : BorTag)
    (offset len : UInt64) (well : map.WellFormed) (bounds : offset.toNat+len.toNat ≤ map.size.bytes.toNat)
    (clean : GeneralRangeMapState.Every (fun row => row.perms.get child = none) map) :
    GeneralRangeMapState.Every (fun row => (RawState row child (GeneralBorrowFreshChild.child tag parent)).permission = .ReservedFrz false)
      (map.modifyRange (Size.ofBytes offset) (Size.ofBytes len) (fun _ row => GeneralBorrowFreshMaterialization.materialized row child GeneralBorrowFreshChild.inside)).state := by
  let predicate := fun row => (RawState row child (GeneralBorrowFreshChild.child tag parent)).permission = .ReservedFrz false
  have initial : GeneralRangeMapState.Every predicate map := by
    intro position valid
    simp only [predicate,RawState,clean position valid,Option.getD_none,TreeNode.defaultLocationState,GeneralBorrowFreshChild.child]
  have prepared := GeneralRangeMapSafety.iter_mut predicate map (Size.ofBytes offset) (Size.ofBytes len) well initial bounds
  rw [GeneralBorrowFreshModify.state_exact map (Size.ofBytes offset) (Size.ofBytes len) _ well bounds]
  have fold : ∀ (positions : List Nat) (current : DedupRangeMap LocationTree),GeneralRangeMapState.Every predicate current →
      GeneralRangeMapState.Every predicate (positions.foldl (fun current position => GeneralBorrowFreshModify.atPosition current position
        (fun _ row => GeneralBorrowFreshMaterialization.materialized row child GeneralBorrowFreshChild.inside)) current) := by
    intro positions
    induction positions with
    | nil => intro current all;exact all
    | cons position rest ih =>
      intro current all
      apply ih
      dsimp only [GeneralBorrowFreshModify.atPosition]
      split
      · rename_i valid
        apply GeneralRangeMapState.replaced_every _ current position valid _ all
        simp only [predicate,RawState,GeneralBorrowFreshMaterialization.materialized,GeneralBorrowFreshLocation.get_same,
          Option.getD_some,GeneralBorrowFreshChild.inside]
      · exact all
  exact fold _ _ prepared.every

private theorem mutable_shape_transport (before after : BorrowTree) (same : treeShape after = treeShape before)
    (child parent : UniIndex) (tag : BorTag)
    (initial : GeneralRangeMapState.Every (fun row => (RawState row child (GeneralBorrowFreshChild.child tag parent)).permission = .ReservedFrz false) before.locations) :
    GeneralRangeMapState.Every (fun row => (RawState row child (GeneralBorrowFreshChild.child tag parent)).permission = .ReservedFrz false) after.locations := by
  have entries := congrArg (fun value => value.2.2.1) same
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    simpa only [treeShape,Array.size_map] using congrArg Array.size entries
  intro position valid
  have oldValid : position < before.locations.entries.size := by omega
  have cell := congrArg (fun rows => rows[position]?) entries
  simp only [treeShape,Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem oldValid,
    Option.map_some,Option.some.injEq,Prod.mk.injEq] at cell
  exact (congrArg Prod.fst (zero_effective_shape _ _ (GeneralBorrowFreshChild.child tag parent) (GeneralBorrowFreshChild.child tag parent) cell.2 rfl child)).trans
    (initial position oldValid)

/-- The actual mutable child has ReservedFrzfalse permission on all rows.
The inside accessed bit is true; SIFA differences remain unconstrained. -/
private theorem mutable_constructor_shape (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ∃ child,actual.tree.indexOfTag newTag = some child ∧
      GeneralRangeMapState.Every (fun row => (RawState row child (GeneralBorrowFreshChild.child newTag parent)).permission = .ReservedFrz false) actual.tree.locations := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have vacant : tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by
      have atEnd : (GeneralBorrowFreshMetadataChildMutable.index input).toNat = tree.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have staged := mutable_shape_modify tree.locations (GeneralBorrowFreshMetadataChildMutable.index input) parent newTag offset len runtime.formed.well bounds
      (by intro position valid;exact (runtime.formed.profile position valid).vacant _ vacant)
    exact ⟨_,(GeneralBorrowFreshMetadataChildMutable.append input).freshLookup,
      mutable_shape_transport (GeneralBorrowFreshMetadataChildMutable.stage input) (GeneralBorrowFreshMetadataChildMutable.result input)
        (GeneralBorrowFreshMetadataChildMutable.shape input) _ parent newTag staged⟩
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have staged := mutable_shape_modify tree.locations index parent newTag offset len runtime.formed.well bounds
      (by intro position valid;exact (runtime.formed.profile position valid).vacant _ vacant)
    exact ⟨index,(GeneralBorrowFreshMetadataChildMutableReuse.reuse input).freshLookup,
      mutable_shape_transport (GeneralBorrowFreshMetadataChildMutableReuse.stage input) (GeneralBorrowFreshMetadataChildMutableReuse.result input)
        (GeneralBorrowFreshMetadataChildMutableReuse.shape input) _ parent newTag staged⟩


private theorem mutable_constructor_permission (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (child : UniIndex) (node : TreeNode)
    (mapped : (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree.indexOfTag newTag=some child)
    (childAt : (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree.nodeAt child=some node) :
    node.defaultInitialPermission=.ReservedFrz false := by
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    let actual := GeneralBorrowFreshMetadataChildMutable.append input
    have same : child=GeneralBorrowFreshMetadataChildMutable.index input := Option.some.inj (mapped.symm.trans actual.freshLookup)
    subst child
    obtain ⟨made,madeAt,_,_,_,permission,_⟩ := actual.newNode
    have eqNode : node=made := Option.some.inj (childAt.symm.trans madeAt)
    exact eqNode ▸ permission
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    let actual := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
    have same : child=index := Option.some.inj (mapped.symm.trans actual.freshLookup)
    subst child
    obtain ⟨made,madeAt,_,_,_,permission,_⟩ := actual.newNode
    have eqNode : node=made := Option.some.inj (childAt.symm.trans madeAt)
    exact eqNode ▸ permission

private theorem mutable_constructor_reserved (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (child : UniIndex) (node : TreeNode)
    (mapped : (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree.indexOfTag newTag=some child)
    (childAt : (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree.nodeAt child=some node) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    GeneralRangeMapState.Every (fun row => (RawState row child node).permission=.ReservedFrz false) actual.tree.locations := by
  dsimp only
  obtain ⟨index,lookup,reserved⟩ := mutable_constructor_shape tree global runtime parentTag newTag parent parentNode tagged present fresh room offset len nonzero bounds
  have same : index=child := Option.some.inj (lookup.symm.trans mapped)
  subst index
  have permission := mutable_constructor_permission tree global runtime parentTag newTag parent parentNode tagged present fresh room offset len nonzero bounds child node mapped childAt
  intro position valid
  have old := reserved position valid
  unfold RawState at old ⊢
  cases stored : (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree.locations.entries[position].data.perms.get child with
  | none => simp only [Option.getD_none,TreeNode.defaultLocationState,permission]
  | some value => simpa only [stored,Option.getD_some] using old

private theorem wildcard_constructor_reserved (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+1≤4294967295)
    (offset len : UInt64) (nonzero : len≠0) (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (child : UniIndex) (node : TreeNode)
    (mapped : (tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree.indexOfTag tag=some child)
    (childAt : (tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree.nodeAt child=some node) :
    let actual := tree.newChild (Size.ofBytes offset) .wildcard tag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    GeneralRangeMapState.Every (fun row => (RawState row child node).permission=.ReservedFrz false) actual.tree.locations := by
  dsimp only
  obtain ⟨mapping,index,inserted,_,vacant,graph,_,_⟩ := GeneralBorrowWildcardConstructorSlot.select tree global runtime tag fresh room (.ReservedFrz false) .None
  have actual := GeneralBorrowWildcardConstructorExact.exact tree runtime.formed.toState tag fresh room mapping index inserted
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside true rfl rfl rfl rfl rfl offset len nonzero bounds
  have atRoot : (WildcardHitZeroConstructor.installed tree mapping index tag (.ReservedFrz false) .None).nodeAt index=
      some (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) := GeneralBorrowFreshLocation.get_same tree.nodes index _
  have rootMapped := graph.allocator.nodeTags index _ atRoot
  rw [actual] at mapped childAt ⊢
  have same : child=index := Option.some.inj (mapped.symm.trans rootMapped)
  subst child
  have sameNode : node=WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None := Option.some.inj (childAt.symm.trans atRoot)
  subst node
  have clean := DuplicatePrefixBorrowContract.vacant_clean runtime index vacant
  have reserved := mutable_shape_modify tree.locations index index tag offset len runtime.formed.well bounds clean
  intro position valid
  have old : (RawState (GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None
      GeneralBorrowFreshChild.inside offset len).locations.entries[position].data index (GeneralBorrowFreshChild.child tag index)).permission=.ReservedFrz false :=
    reserved position valid
  unfold RawState at old ⊢
  cases stored : (GeneralBorrowPositiveWildcardConstructor.result tree mapping index tag (.ReservedFrz false) .None GeneralBorrowFreshChild.inside offset len).locations.entries[position].data.perms.get index with
  | none => simp only [Option.getD_none,TreeNode.defaultLocationState,WildcardHitZeroConstructor.rootNode]
  | some value => simpa only [stored,Option.getD_some] using old

private theorem complete_prepared_read (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (node : TreeNode) (present : tree.nodes.get pointer.grant = some node)
    (provenance : match pointer.value.provenance with | .concrete _ tag => tag=node.tag | .wildcard => node.isExposed=true)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (short : tree.nodes.size < 65536) (offset : UInt64) (bounds : offset.toNat+1 ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+1) tree.locations) :
    let output := CurrentCallTypedFnEntry.literal tree global frame allocation room pointer.value.provenance offset 1
    DuplicatePrefixBorrowContract.RuntimeFacts output.access.tree output.global ∧
      Completes output.access.tree completion ∧ output.access.tree.nodes=tree.nodes ∧
      output.access.tree.tagMapping=tree.tagMapping ∧ output.access.tree.locations.size=tree.locations.size := by
  obtain ⟨position,root,rootNode,slot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path tree runtime.formed.toGraphState pointer.grant node present
  cases prov : pointer.value.provenance with
  | concrete id tag =>
    have tagEq : tag=node.tag := by simpa only [prov] using provenance
    obtain ⟨_,afterRuntime,afterComplete,_,nodes,_,tags,capacity⟩ := S05ConcreteFnEntryRaw.prepare_read tree global frame allocation completion runtime complete order
      position root pointer.grant rootNode node slot rootAt present path room offset 1 bounds owned short .VisitChildrenOfAccessed
    simpa only [CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov,tagEq]
      using And.intro afterRuntime (And.intro afterComplete (And.intro nodes (And.intro tags capacity)))
  | wildcard =>
    have exposed : node.isExposed=true := by simpa only [prov] using provenance
    obtain ⟨_,afterRuntime,afterComplete,_,nodes,_,tags,capacity⟩ := S05WildcardFnEntryRaw.prepare_read tree global frame allocation completion runtime complete order
      position root pointer.grant rootNode node slot rootAt present exposed path room offset 1 bounds owned short .VisitChildrenOfAccessed
    simpa only [CurrentCallTypedFnEntry.literal,CurrentCallTypedFnEntry.parent,CandidateCurrentWindowPointerChecks.extraOf,prov]
      using And.intro afterRuntime (And.intro afterComplete (And.intro nodes (And.intro tags capacity)))

private theorem complete_constructor_reserved (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (node : TreeNode) (present : tree.nodes.get pointer.grant=some node)
    (provenance : match pointer.value.provenance with | .concrete _ tag => tag=node.tag | .wildcard => node.isExposed=true)
    (room : global.nextPointerTag.value<18446744073709551615)
    (nodeRoom : tree.nodes.size+1≤4294967295) (short : tree.nodes.size+1<65536)
    (offset : UInt64) (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+1) tree.locations)
    (borrow : CurrentCallEmptyEntryCompleteRelease.Result tree global frame allocation completion pointer offset room) :
    GeneralRangeMapState.Every (fun row => (RawState row borrow.child borrow.node).permission=.ReservedFrz false) borrow.output.child.tree.locations := by
  let literal := CurrentCallTypedFnEntry.literal tree global frame allocation room pointer.value.provenance offset 1
  have outputEq : borrow.output=literal := Except.ok.inj (borrow.actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ room _ _ _))
  obtain ⟨readRuntime,_,readNodes,readTags,readCapacity⟩ := complete_prepared_read tree global frame allocation completion runtime complete order pointer node present provenance
    room (by omega) offset bounds owned
  change DuplicatePrefixBorrowContract.RuntimeFacts literal.access.tree literal.global at readRuntime
  change literal.access.tree.nodes=tree.nodes at readNodes
  change literal.access.tree.tagMapping=tree.tagMapping at readTags
  change literal.access.tree.locations.size=tree.locations.size at readCapacity
  rw [←outputEq] at readRuntime readNodes readTags readCapacity
  have fresh := (GeneralBorrowFnEntryRegistrationRuntime.prepare tree global frame allocation room runtime).2.2.2.2.2
  have freshRead : GeneralBorrowTagMap.Fresh borrow.output.access.tree.tagMapping global.nextPointerTag := by rw [readTags];exact fresh
  have readRoom : borrow.output.access.tree.nodes.size+1≤4294967295 := by rw [readNodes];exact nodeRoom
  have readBounds : offset.toNat+1≤borrow.output.access.tree.locations.size.bytes.toNat := by rw [readCapacity];exact bounds
  have readPresent : borrow.output.access.tree.nodeAt pointer.grant=some node := by change borrow.output.access.tree.nodes.get pointer.grant=_;rw [readNodes];exact present
  have childEq : borrow.output.child=borrow.output.access.tree.newChild (Size.ofBytes offset)
      (CandidateCurrentWindowPointerChecks.extraOf pointer.value.provenance) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 1) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true := by rw [outputEq];rfl
  have mapped := borrow.lookup
  have childAt := borrow.childAt
  rw [childEq,borrow.tag] at mapped
  rw [childEq] at childAt ⊢
  cases kind : pointer.value.provenance with
  | concrete id tag =>
    have tagEq : tag=node.tag := by simpa only [kind] using provenance
    have tagged : borrow.output.access.tree.indexOfTag tag=some pointer.grant := by
      rw [tagEq];exact readRuntime.formed.allocator.nodeTags pointer.grant node readPresent
    apply mutable_constructor_reserved borrow.output.access.tree borrow.output.global readRuntime tag global.nextPointerTag pointer.grant node tagged readPresent freshRead readRoom offset 1 (by decide) readBounds borrow.child borrow.node
    · simpa only [CandidateCurrentWindowPointerChecks.extraOf,kind] using mapped
    · simpa only [CandidateCurrentWindowPointerChecks.extraOf,kind] using childAt
  | wildcard =>
    apply wildcard_constructor_reserved borrow.output.access.tree borrow.output.global readRuntime global.nextPointerTag freshRead readRoom offset 1 (by decide) readBounds borrow.child borrow.node
    · simpa only [CandidateCurrentWindowPointerChecks.extraOf,kind] using mapped
    · simpa only [CandidateCurrentWindowPointerChecks.extraOf,kind] using childAt

private theorem zero_associated_read (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (complete : Completes tree completion) (oldFormed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (nextOrder : ParentTagOrder (slot.after tag)) (distinct : (slot.after tag).roots.toList.Nodup)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts (slot.after tag) global)
    (position : Nat) (root source : UniIndex) (rootNode sourceNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePresent : tree.nodes.get source = some sourceNode)
    (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root source)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (clean : GeneralBorrowFreshFutureClean.Clean tree slot.index)
    (offset len : UInt64) (bounds : offset.toNat+len.toNat ≤ (slot.after tag).locations.size.bytes.toNat)
    (owned : OwnedOn (ZeroRights tree slot tag completion global.protectedTags source) offset (offset+len) (slot.after tag).locations)
    (short : (slot.after tag).nodes.size < 65536) :
    let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation room
    let read := (slot.after tag).performBorrowAccessRange (.concrete sourceNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read registration.1.protectedTags .VisitChildrenOfAccessed
    read.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts read.tree registration.1 ∧
      OwnedOn (ZeroRights tree slot tag completion registration.1.protectedTags source) offset (offset+len) read.tree.locations ∧
      OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal read.tree location registration.1.protectedTags source))
        offset (offset+len) read.tree.locations ∧
      read.tree = {(slot.after tag) with locations := read.tree.locations} ∧ read.tree.locations.size = (slot.after tag).locations.size ∧
      GeneralRangeMapState.Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location slot.index
        (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).accessed = false) read.tree.locations := by
  obtain ⟨_,_,_,registeredRuntime,nodeFresh,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare (slot.after tag) global frame allocation room runtime
  let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation room
  let read := (slot.after tag).performBorrowAccessRange (.concrete sourceNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  have flags (index : UniIndex) (node : TreeNode) (present : (slot.after tag).nodes.get index = some node) :
      registration.1.protectedTags.contains node.tag = global.protectedTags.contains node.tag := by
    exact ProtectorInsertion.contains_other global.protectedTags global.nextPointerTag node.tag .StrongProtector
      (nodeFresh (index,node) (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get (slot.after tag).nodes index node).mpr present)))
  have rowInput : OwnedOn (fun location => location.perms.get slot.index = none ∧
      ZeroRights tree slot tag completion registration.1.protectedTags source location) offset (offset+len) (slot.after tag).locations := by
    intro cursor valid positive start stop
    refine ⟨clean cursor valid,?_,?_⟩
    · intro index node present
      rw [flags index node (S04ZeroRootObserverNormal.old_node tree slot tag index node present)]
      exact (owned cursor valid positive start stop).1 index node present
    · have flag := flags slot.index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) (GeneralBorrowFreshLocation.get_same _ _ _)
      change registration.1.protectedTags.contains tag = global.protectedTags.contains tag at flag
      rw [flag]
      exact (owned cursor valid positive start stop).2
  have mapped : (slot.after tag).indexOfTag sourceNode.tag = some source :=
    registeredRuntime.formed.allocator.nodeTags source sourceNode (S04ZeroRootObserverNormal.old_node tree slot tag source sourceNode sourcePresent)
  have range := zero_concrete_range tree slot tag completion registration.1.protectedTags complete oldFormed registeredRuntime.formed.toGraphState
    depth order nextOrder distinct position root source rootNode sourceNode rootSlot rootPresent sourcePath mapped
    (Size.ofBytes offset) (Size.ofBytes len) offset (offset+len) rowInput registeredRuntime.formed.well
    (fun cursor valid => ⟨registeredRuntime.coherent cursor valid,registeredRuntime.formed.profile cursor valid,registeredRuntime.possible cursor valid⟩)
    bounds (Nat.le_refl _) (Nat.le_refl _) short .VisitChildrenOfAccessed
  have same : read.tree = {(slot.after tag) with locations := read.tree.locations} := range.tree_eq
  have afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts read.tree registration.1 := by
    rw [same]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations (slot.after tag) _ registeredRuntime.formed.toGraphState,range.well⟩,?_⟩,?_,?_,
      ⟨registeredRuntime.below.mapping,registeredRuntime.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(range.runtime cursor valid).2.1.present,(range.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid
      exact (range.runtime cursor valid).1
    · intro cursor valid
      exact (range.runtime cursor valid).2.2
  have fits : tree.nodes.data.size ≤ 4294967296 := by
    have growth := slot.size tag
    rw [growth] at short
    change tree.nodes.data.size+slot.growth < 65536 at short
    omega
  have normals := zero_parent_normal_owned tree slot tag completion registration.1.protectedTags complete oldFormed depth fits
    position root source rootNode rootSlot rootPresent sourcePath read.tree.locations offset (offset+len) range.rows
  refine ⟨range.completed,afterRuntime,range.rows,?_,same,range.capacity,?_⟩
  · rw [same]
    exact normals
  · let zeroNode := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
    have zeroAt : (slot.after tag).nodeAt slot.index = some zeroNode := GeneralBorrowFreshLocation.get_same _ _ _
    have different : slot.index ≠ source := by intro same;rw [←same,slot.vacant] at sourcePresent;cases sourcePresent
    have inactive : GeneralRangeMapState.Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location slot.index zeroNode).accessed = false)
        (slot.after tag).locations := by
      intro cursor valid
      change ((tree.locations.entries[cursor].data.perms.get slot.index).getD zeroNode.defaultLocationState).accessed = false
      rw [clean cursor valid]
      rfl
    have initialRights : OwnedOn (ZeroRights tree slot tag completion registration.1.protectedTags source) offset (offset+len) (slot.after tag).locations := by
      intro cursor valid positive start stop
      exact (rowInput cursor valid positive start stop).2
    have initialNormals := zero_parent_normal_owned tree slot tag completion registration.1.protectedTags complete oldFormed depth fits
      position root source rootNode rootSlot rootPresent sourcePath (slot.after tag).locations offset (offset+len) initialRights
    exact CurrentCallEmptyEntryQuietRelease.concrete (slot.after tag) registration.1 registeredRuntime sourceNode.tag source slot.index offset len bounds
      initialNormals sourceNode (S04ZeroRootObserverNormal.old_node tree slot tag source sourceNode sourcePresent) mapped zeroNode zeroAt rfl rfl different inactive .Read .VisitChildrenOfAccessed


private theorem zero_fnentry (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (complete : Completes tree completion) (oldFormed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (nextOrder : ParentTagOrder (slot.after tag)) (distinct : (slot.after tag).roots.toList.Nodup)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts (slot.after tag) global)
    (position : Nat) (root source : UniIndex) (rootNode sourceNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePresent : tree.nodes.get source = some sourceNode)
    (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root source)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : (slot.after tag).nodes.size+1 ≤ 4294967295)
    (clean : GeneralBorrowFreshFutureClean.Clean tree slot.index)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ (slot.after tag).locations.size.bytes.toNat)
    (owned : OwnedOn (ZeroRights tree slot tag completion global.protectedTags source) offset (offset+len) (slot.after tag).locations)
    (short : (slot.after tag).nodes.size < 65536) :
    ∃ output : GeneralBorrowForestFnEntry.Output,
      GeneralBorrowForestFnEntry.operation (slot.after tag) global frame allocation sourceNode.tag offset len .VisitChildrenOfAccessed = .ok output ∧
      output.tag = global.nextPointerTag ∧ output.global = (GeneralBorrowFnEntryRegistration.registered global frame allocation room).1 ∧
      output.frame = (GeneralBorrowFnEntryRegistration.registered global frame allocation room).2 ∧
      output.access = (slot.after tag).performBorrowAccessRange (.concrete sourceNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
        .Read output.global.protectedTags .VisitChildrenOfAccessed ∧
      output.access.tree = {(slot.after tag) with locations := output.access.tree.locations} ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.access.tree output.global ∧
      output.access.tree.locations.size = (slot.after tag).locations.size ∧
      output.child = output.access.tree.newChild (Size.ofBytes offset) (.concrete sourceNode.tag) output.tag
        (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = (slot.after tag).locations.size ∧ output.child.tree.nodes.size ≤ (slot.after tag).nodes.size+1 ∧
      ParentTagOrder output.child.tree ∧
      OwnedOn (ZeroRights tree slot tag completion output.global.protectedTags source) offset (offset+len) output.child.tree.locations ∧
      ∃ child, output.child.tree.indexOfTag output.tag = some child ∧
        OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal output.child.tree location output.global.protectedTags child))
          offset (offset+len) output.child.tree.locations ∧
        GeneralRangeMapState.Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location slot.index
          (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).accessed = false) output.access.tree.locations ∧
        GeneralRangeMapState.Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location slot.index
          (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).accessed = false) output.child.tree.locations := by
  obtain ⟨allocated,held,_,_,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare (slot.after tag) global frame allocation room runtime
  let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation room
  let read := (slot.after tag).performBorrowAccessRange (.concrete sourceNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨readDone,readRuntime,readOwned,readNormals,same,capacity,readInactive⟩ := zero_associated_read tree slot tag completion global frame allocation
    complete oldFormed depth order nextOrder distinct runtime position root source rootNode sourceNode rootSlot rootPresent sourcePresent sourcePath
    room clean offset len bounds owned short
  have nodes : read.tree.nodes = (slot.after tag).nodes := by rw [same]
  have tags : read.tree.tagMapping = (slot.after tag).tagMapping := by rw [same]
  have present : read.tree.nodes.get source = some sourceNode := by
    rw [nodes]
    exact S04ZeroRootObserverNormal.old_node tree slot tag source sourceNode sourcePresent
  have tagged : read.tree.indexOfTag sourceNode.tag = some source := readRuntime.formed.allocator.nodeTags source sourceNode present
  have freshAfter : GeneralBorrowTagMap.Fresh read.tree.tagMapping global.nextPointerTag := by rw [tags];exact fresh
  have afterRoom : read.tree.nodes.size+1 ≤ 4294967295 := by rw [nodes];exact nodeRoom
  have afterBounds : offset.toNat+len.toNat ≤ read.tree.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have tagBound : global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag room
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag room).value.toNat
    omega
  have heldTag : registration.1.protectedTags.contains global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  obtain ⟨childDone,childRuntime,childCapacity,growth,child,lookup,normals⟩ := CurrentCallEmptyEntryBoolChildNormal.construct read.tree registration.1 readRuntime
    sourceNode.tag global.nextPointerTag source sourceNode tagged present freshAfter afterRoom tagBound heldTag offset len nonzero afterBounds readNormals
  have rawAfter := zero_rights_child_owned tree slot tag completion registration.1.protectedTags source read.tree registration.1 nodes readRuntime
    sourceNode.tag global.nextPointerTag source sourceNode tagged present freshAfter afterRoom offset len nonzero afterBounds readOwned
  let zeroNode := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
  have zeroAt : read.tree.nodes.get slot.index = some zeroNode := by
    rw [nodes]
    exact GeneralBorrowFreshLocation.get_same _ _ _
  have childInactive := CurrentCallEmptyEntryQuietRelease.construct read.tree registration.1 readRuntime
    sourceNode.tag global.nextPointerTag source sourceNode tagged present freshAfter afterRoom offset len nonzero afterBounds
    slot.index zeroNode zeroAt readInactive
  have readOrder := GeneralBorrowParentTagInvariant.nodes_frame (slot.after tag) read.tree nodes nextOrder
  have older := GeneralBorrowParentTagInvariant.parent_below_fresh (slot.after tag) global runtime source sourceNode
    (S04ZeroRootObserverNormal.old_node tree slot tag source sourceNode sourcePresent)
  have childOrder := GeneralBorrowProtectedChildOrder.construct read.tree registration.1 readRuntime readOrder
    sourceNode.tag global.nextPointerTag source sourceNode tagged present freshAfter afterRoom
    (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp older))) offset len nonzero afterBounds
  let output : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,global.nextPointerTag,read,
    read.tree.newChild (Size.ofBytes offset) (.concrete sourceNode.tag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩
  have totalGrowth : output.child.tree.nodes.size ≤ (slot.after tag).nodes.size+1 := by
    rw [nodes] at growth
    exact growth
  refine ⟨output,?_,rfl,rfl,rfl,rfl,same,readRuntime,capacity,rfl,readDone,childDone,childRuntime,childCapacity.trans capacity,totalGrowth,childOrder,rawAfter,child,lookup,normals,readInactive,childInactive⟩
  simp only [GeneralBorrowForestFnEntry.operation,allocated,Except.bind,Except.pure,bind,pure]
  rfl


private theorem zero_write_authorization (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (protections : ProtectedTags) (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree selected source)
    (child : UniIndex) (newNode : TreeNode) (vacant : (slot.after tag).nodes.get child = none) (hidden : newNode.isExposed = false)
    (size : (slot.after tag).nodes.size ≤ (attachedNodes (slot.after tag).nodes child source sourceNode newNode).size)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (nextDepth : GeneralBorrowExposure.ParentDepth (attachedNodes (slot.after tag).nodes child source sourceNode newNode))
    (initial current : LocationTree) (initialRights : ZeroRights tree slot tag completion protections source initial)
    (position : Nat) (root : UniIndex) (rootAt : (slot.after tag).roots[position]? = some root) (different : root ≠ selected)
    (frame : ∀ index node, ({(slot.after tag) with nodes := attachedNodes (slot.after tag).nodes child source sourceNode newNode,tagMapping := mapping,locations := locations} : BorrowTree).nodes.get index = some node →
      GeneralBorrowExposedNonleafPrimaryPath.Path {(slot.after tag) with nodes := attachedNodes (slot.after tag).nodes child source sourceNode newNode,tagMapping := mapping,locations := locations} root index → current.perms.get index = initial.perms.get index)
    (consistent : ∀ index node, ({(slot.after tag) with nodes := attachedNodes (slot.after tag).nodes child source sourceNode newNode,tagMapping := mapping,locations := locations} : BorrowTree).nodes.get index = some node →
      GeneralBorrowExposedNonleafPrimaryPath.Path {(slot.after tag) with nodes := attachedNodes (slot.after tag).nodes child source sourceNode newNode,tagMapping := mapping,locations := locations} root index →
      GeneralBorrowSifaPermissionConsistency.Consistent ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) :
    DuplicatePrefixResidualWriteRepaired.Authorization {(slot.after tag) with nodes := attachedNodes (slot.after tag).nodes child source sourceNode newNode,tagMapping := mapping,locations := locations} current protections root position (some selectedNode.tag) .Write
      (fun query => if position < tree.roots.size then GeneralBorrowExposedNonleafPrimaryPath.Path tree root query else query = slot.index) := by
  let nextTree := {(slot.after tag) with nodes := attachedNodes (slot.after tag).nodes child source sourceNode newNode,tagMapping := mapping,locations := locations}
  have parentAt := S04ZeroRootObserverNormal.old_node tree slot tag source sourceNode sourcePresent
  have parents := GeneralBorrowSharedCallbacksAttach.parents (slot.after tag) child source sourceNode newNode vacant parentAt
  have extend (other index : UniIndex) (path : GeneralBorrowExposedNonleafPrimaryPath.Path tree other index) :
      GeneralBorrowExposedNonleafPrimaryPath.Path nextTree other index := by
    apply GeneralBorrowSharedAuthorizationGeometry.path_extension (slot.after tag) nextTree parents other index
    apply GeneralBorrowSharedAuthorizationGeometry.path_extension tree (slot.after tag) _ other index path
    intro query node present
    exact ⟨node,S04ZeroRootObserverNormal.old_node tree slot tag query node present,rfl⟩
  change (tree.roots.push slot.index)[position]? = some root at rootAt
  by_cases oldPosition : position < tree.roots.size
  · have oldSlot : tree.roots[position]? = some root := by
      simpa only [Array.getElem?_push,ite_eq_right (Nat.ne_of_lt oldPosition)] using rootAt
    have notParent : ¬GeneralBorrowExposedNonleafPrimaryPath.Path tree root source := by
      intro path
      obtain ⟨rootNode,rootPresent,rootParentless⟩ := complete.2.2.2.1 position root oldSlot
      obtain ⟨selectedActual,selectedAt,selectedParentless⟩ := complete.2.2.2.1 selectedPosition selected selectedSlot
      exact different (CompletedBorrowAncestry.physical_roots_unique rootPresent rootParentless selectedAt selectedParentless path sourcePath)
    have unchanged (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
        (path : GeneralBorrowExposedNonleafPrimaryPath.Path tree root index) : nextTree.nodes.get index = some node := by
      have notChild : index ≠ child := by
        intro same
        have nextAt := S04ZeroRootObserverNormal.old_node tree slot tag index node present
        change (slot.after tag).nodes.get index = some node at nextAt
        rw [same,vacant] at nextAt
        cases nextAt
      have notSource : index ≠ source := by intro same;subst index;exact notParent path
      change (((slot.after tag).nodes.insert child newNode).insert source {sourceNode with children := sourceNode.children.push child}).get index = some node
      rw [GeneralBorrowFreshLocation.get_other _ source index _ notSource,GeneralBorrowFreshLocation.get_other _ child index _ notChild]
      exact S04ZeroRootObserverNormal.old_node tree slot tag index node present
    have currentRights (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
        (path : GeneralBorrowExposedNonleafPrimaryPath.Path tree root index) := by
      have scalar := initialRights.1 index node present
      rw [←frame index node (unchanged index node present path) (extend root index path)] at scalar
      exact scalar
    have initialAuth := S05CompletedAncestryWriteAccess.authorization tree completion current protections complete depth order position selectedPosition
      root selected source selectedNode oldSlot selectedSlot selectedPresent different sourcePath
      (fun index node present path => (currentRights index node present path).1)
      (fun index node present path => (currentRights index node present path).2)
      (fun index node present path => consistent index node (unchanged index node present path) (extend root index path))
    have zeroAuth := CurrentCallEmptyEntryZeroRootQueries.old_write tree slot tag depth current protections root position (some selectedNode.tag)
      (GeneralBorrowExposedNonleafPrimaryPath.Path tree root) initialAuth
    have auth := CurrentCallEmptyEntryZeroRootQueries.old_write_after_child (slot.after tag) (slot.depth depth tag)
      child source sourceNode newNode vacant parentAt hidden size mapping locations current current protections (by intros;rfl)
      root position (some selectedNode.tag) (GeneralBorrowExposedNonleafPrimaryPath.Path tree root) zeroAuth notParent nextDepth
    simpa only [ite_eq_left oldPosition] using auth
  · have positionEq : position = tree.roots.size := by
      by_cases equal : position = tree.roots.size
      · exact equal
      · simp only [Array.getElem?_push,ite_eq_right equal] at rootAt
        rw [Array.getElem?_eq_none (by omega)] at rootAt
        cases rootAt
    subst position
    have rootEq : slot.index = root := by simpa only [Array.getElem?_push,↓reduceIte,Option.some.injEq] using rootAt
    subst root
    let zeroNode := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
    have zeroAt : nextTree.nodes.get slot.index = some zeroNode := by
      have notParent : slot.index ≠ source := by intro same;rw [←same,slot.vacant] at sourcePresent;cases sourcePresent
      have notChild : slot.index ≠ child := by
        intro same
        have atZero : (slot.after tag).nodes.get slot.index = some zeroNode := GeneralBorrowFreshLocation.get_same _ _ _
        rw [same,vacant] at atZero
        cases atZero
      change (((slot.after tag).nodes.insert child newNode).insert source _).get slot.index = some zeroNode
      rw [GeneralBorrowFreshLocation.get_other _ source slot.index _ notParent,GeneralBorrowFreshLocation.get_other _ child slot.index _ notChild]
      exact GeneralBorrowFreshLocation.get_same _ _ _
    have foreign : OrdinaryBorrowAuthority.ForeignWrite ((current.perms.get slot.index).getD zeroNode.defaultLocationState) (protections.contains tag) := by
      rw [frame slot.index zeroNode zeroAt (.refl slot.index zeroNode zeroAt)]
      exact initialRights.2
    have nonempty : 0 < tree.roots.size := by have bound := (Array.getElem?_eq_some_iff.mp selectedSlot).1;omega
    have zeroAuth := CurrentCallEmptyEntryZeroRootQueries.new_foreign tree slot tag depth current protections nonempty (some selectedNode.tag) .Write
      foreign (consistent slot.index zeroNode zeroAt (.refl slot.index zeroNode zeroAt))
    have notParent : ¬source = slot.index := by intro same;rw [same,slot.vacant] at sourcePresent;cases sourcePresent
    have auth := CurrentCallEmptyEntryZeroRootQueries.old_write_after_child (slot.after tag) (slot.depth depth tag)
      child source sourceNode newNode vacant parentAt hidden size mapping locations current current protections (by intros;rfl)
      slot.index tree.roots.size (some selectedNode.tag) (fun query => query = slot.index) zeroAuth notParent nextDepth
    simpa only [ite_eq_right (Nat.lt_irrefl tree.roots.size)] using auth


private abbrev boolStage (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (child source : UniIndex) (sourceNode newNode : TreeNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) : BorrowTree :=
  {(slot.after tag) with nodes := attachedNodes (slot.after tag).nodes child source sourceNode newNode,tagMapping := mapping,locations := locations}
private abbrev boolAfter (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (child source : UniIndex) (sourceNode newNode : TreeNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree) : BorrowTree :=
  (sourceUpdateSifa (boolStage tree slot tag child source sourceNode newNode mapping locations) source .None).1


private theorem boolAfter_old_node (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (child source : UniIndex) (sourceNode newNode : TreeNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (vacant : (slot.after tag).nodes.get child = none) (sourceAt : tree.nodes.get source = some sourceNode)
    (index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node) :
    ∃ next,(boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get index = some next ∧
      next.tag = node.tag ∧ next.parent = node.parent ∧ next.defaultInitialPermission = node.defaultInitialPermission ∧ next.isExposed = node.isExposed := by
  let stage := boolStage tree slot tag child source sourceNode newNode mapping locations
  have notChild : index ≠ child := by
    intro same
    have oldAt : (slot.after tag).nodes.get index = some node := S04ZeroRootObserverNormal.old_node tree slot tag index node present
    rw [same,vacant] at oldAt
    cases oldAt
  have staged : ∃ next,stage.nodes.get index = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧
      next.defaultInitialPermission = node.defaultInitialPermission ∧ next.isExposed = node.isExposed := by
    by_cases parent : index = source
    · subst index
      have equal : node = sourceNode := Option.some.inj (present.symm.trans sourceAt)
      subst node
      exact ⟨{sourceNode with children := sourceNode.children.push child},GeneralBorrowFreshLocation.get_same _ _ _,rfl,rfl,rfl,rfl⟩
    · refine ⟨node,?_,rfl,rfl,rfl,rfl⟩
      change (((slot.after tag).nodes.insert child newNode).insert source _).get index = some node
      rw [GeneralBorrowFreshLocation.get_other _ source index _ parent,GeneralBorrowFreshLocation.get_other _ child index _ notChild]
      exact S04ZeroRootObserverNormal.old_node tree slot tag index node present
  obtain ⟨stagedNode,stagedAt,tagEq,parentEq,permissionEq,exposureEq⟩ := staged
  obtain ⟨next,nextAt,nextTag,nextParent,_,nextPermission,nextExposure⟩ :=
    GeneralBorrowFreshMetadataChildSifa.node_fields stage source .None index stagedNode stagedAt
  exact ⟨next,nextAt,nextTag.trans tagEq,nextParent.trans parentEq,nextPermission.trans permissionEq,nextExposure.trans exposureEq⟩

private theorem boolAfter_child_node (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (child source : UniIndex) (sourceNode newNode : TreeNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (vacant : (slot.after tag).nodes.get child = none) (sourceAt : tree.nodes.get source = some sourceNode) :
    ∃ next,(boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get child = some next ∧
      next.tag = newNode.tag ∧ next.parent = newNode.parent ∧ next.children = newNode.children ∧ next.isExposed = newNode.isExposed ∧ next.defaultInitialPermission = newNode.defaultInitialPermission := by
  let stage := boolStage tree slot tag child source sourceNode newNode mapping locations
  have different : child ≠ source := by
    intro same
    have oldAt : (slot.after tag).nodes.get source = some sourceNode := S04ZeroRootObserverNormal.old_node tree slot tag source sourceNode sourceAt
    rw [←same,vacant] at oldAt
    cases oldAt
  have stagedAt : stage.nodes.get child = some newNode := by
    change (((slot.after tag).nodes.insert child newNode).insert source _).get child = some newNode
    rw [GeneralBorrowFreshLocation.get_other _ source child _ different]
    exact GeneralBorrowFreshLocation.get_same _ _ _
  obtain ⟨next,nextAt,tagEq,parentEq,childrenEq,permissionEq,exposureEq⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields stage source .None child newNode stagedAt
  exact ⟨next,nextAt,tagEq,parentEq,childrenEq,exposureEq,permissionEq⟩


/-- Exact legal-mask/query transport through the actual two hidden nodes and SIFA pass. -/
private theorem boolAfter_query (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (child source : UniIndex) (sourceNode newNode : TreeNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (vacant : (slot.after tag).nodes.get child = none) (sourceAt : tree.nodes.get source = some sourceNode)
    (hidden : newNode.isExposed = false)
    (size : (slot.after tag).nodes.size ≤ (attachedNodes (slot.after tag).nodes child source sourceNode newNode).size)
    (current : LocationTree) (protections : ProtectedTags) (root query : UniIndex) (position : Nat)
    (maximum : Option BorTag) (node : TreeNode) (removed : List UniIndex)
    (legal : DuplicatePrefixResidualSupportAuthorization.Removal
      (boolAfter tree slot tag child source sourceNode newNode mapping locations) current protections maximum .Write removed) :
    DuplicatePrefixResidualSupportAuthorization.Removal tree current protections maximum .Write removed ∧
      DuplicatePrefixResidualSupportAuthorization.residualRelation
        (boolAfter tree slot tag child source sourceNode newNode mapping locations) current protections root query node maximum .Write position removed =
      DuplicatePrefixResidualSupportAuthorization.residualRelation tree current protections root query node maximum .Write position removed := by
  let stage := boolStage tree slot tag child source sourceNode newNode mapping locations
  let after := boolAfter tree slot tag child source sourceNode newNode mapping locations
  have shape : treeShape after = treeShape stage := GeneralBorrowSifaView.preserves stage source .None
  have growth : tree.nodes.size ≤ after.nodes.size := by
    rw [GeneralBorrowFreshMetadata.node_size stage after shape]
    exact Nat.le_trans (by rw [slot.size tag];omega) size
  apply CurrentCallEmptyEntryWriteRetention.metadata_query tree after current current protections depth growth _ _ root query position maximum node removed legal
  · intro index original present
    obtain ⟨next,nextAt,nextTag,nextParent,nextPermission,nextExposure⟩ :=
      boolAfter_old_node tree slot tag child source sourceNode newNode mapping locations vacant sourceAt index original present
    exact ⟨next,nextAt,nextParent,nextTag,nextExposure,
      congrArg Prod.fst (GeneralBorrowSifaWritableFrame.effective_shape current current index original next rfl nextPermission)⟩
  · intro index next nextAt exposed
    have exposure := GeneralBorrowFreshMetadataChildSifa.lookup_exposure stage after
      (GeneralBorrowFreshMetadataChildSifa.sifa_exposure stage source .None) index
    rw [nextAt] at exposure
    simp only [Option.map_some,exposed] at exposure
    cases stagedAt : stage.nodes.get index with
    | none => rw [stagedAt] at exposure;cases exposure
    | some staged =>
      have stagedExposure : staged.isExposed = true := by
        rw [stagedAt] at exposure
        exact Option.some.inj exposure.symm
      have notChild : index ≠ child := by
        intro same
        subst index
        have different : child ≠ source := by
          intro same
          have atSource := S04ZeroRootObserverNormal.old_node tree slot tag source sourceNode sourceAt
          change (slot.after tag).nodes.get source = some sourceNode at atSource
          rw [←same,vacant] at atSource;cases atSource
        change (((slot.after tag).nodes.insert child newNode).insert source _).get child = some staged at stagedAt
        rw [GeneralBorrowFreshLocation.get_other _ source child _ different,GeneralBorrowFreshLocation.get_same] at stagedAt
        cases stagedAt
        rw [hidden] at stagedExposure
        contradiction
      by_cases sameSource : index = source
      · subst index
        exact ⟨sourceNode,sourceAt⟩
      · have oldAt : (slot.after tag).nodes.get index = some staged := by
          change (((slot.after tag).nodes.insert child newNode).insert source _).get index = some staged at stagedAt
          rw [GeneralBorrowFreshLocation.get_other _ source index _ sameSource,
            GeneralBorrowFreshLocation.get_other _ child index _ notChild] at stagedAt
          exact stagedAt
        have notZero : index ≠ slot.index := by
          intro same
          subst index
          change (tree.nodes.insert slot.index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).get slot.index = some staged at oldAt
          rw [GeneralBorrowFreshLocation.get_same] at oldAt
          cases oldAt
          cases stagedExposure
        refine ⟨staged,?_⟩
        change (tree.nodes.insert slot.index _).get index = some staged at oldAt
        rw [GeneralBorrowFreshLocation.get_other _ slot.index index _ notZero] at oldAt
        exact oldAt


/-- The partial completion adds only the REAL Bool parent edge. -/
private theorem boolChild_ancestry (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (complete : Completes tree completion) (child source : UniIndex)
    (vacant : (slot.after tag).nodes.get child = none) (sourceNode : TreeNode) (sourceAt : tree.nodes.get source = some sourceNode) :
    (∀ index node,tree.nodes.get index = some node →
      (Below (S05ConcreteProtectedChildCompletion.extend completion child source) index child ↔ Below completion index source)) ∧
    ¬Below (S05ConcreteProtectedChildCompletion.extend completion child source) slot.index child := by
  have oldVacant : tree.nodes.get child = none := by
    cases present : tree.nodes.get child with
    | none => rfl
    | some node =>
      have nextAt := S04ZeroRootObserverNormal.old_node tree slot tag child node present
      change (slot.after tag).nodes.get child = some node at nextAt
      rw [vacant] at nextAt;cases nextAt
  have parentLive : ∃ node,tree.nodes.get source = some node := ⟨sourceNode,sourceAt⟩
  have ancestry (index : UniIndex) := S05ConcreteProtectedChildCompletion.child_ancestry_iff tree completion complete child source oldVacant parentLive index
  constructor
  · intro index node present
    have different : index ≠ child := by intro same;rw [same,oldVacant] at present;cases present
    simpa only [different,false_or] using ancestry index
  · intro path
    rcases (ancestry slot.index).mp path with same | old
    · have nextAt : (slot.after tag).nodes.get slot.index = some (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) := GeneralBorrowFreshLocation.get_same _ _ _
      rw [same,vacant] at nextAt;cases nextAt
    · have ancestorLive : ∀ {first last : UniIndex},Below completion first last →
          (∃ node,tree.nodes.get last = some node) → ∃ node,tree.nodes.get first = some node := by
        intro first last walk
        induction walk with
        | refl => exact id
        | @step predecessor target edge earlier ih =>
          intro _
          exact ih (complete.2.2.2.2.2.2 target predecessor edge).2.1
      obtain ⟨node,present⟩ := ancestorLive old parentLive
      rw [slot.vacant] at present;cases present


private theorem boolAfter_cases (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (child source : UniIndex) (sourceNode newNode : TreeNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (sourceAt : tree.nodes.get source = some sourceNode) (index : UniIndex) (node : TreeNode)
    (present : (boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get index = some node) :
    index = child ∨ index = slot.index ∨ ∃ old,tree.nodes.get index = some old := by
  let stage := boolStage tree slot tag child source sourceNode newNode mapping locations
  let after := boolAfter tree slot tag child source sourceNode newNode mapping locations
  have shape : treeShape after = treeShape stage := GeneralBorrowSifaView.preserves stage source .None
  obtain ⟨staged,stagedAt,_⟩ := GeneralBorrowFreshMetadata.node_exists after stage shape.symm index node present
  by_cases isChild : index = child
  · exact Or.inl isChild
  by_cases isZero : index = slot.index
  · exact Or.inr (Or.inl isZero)
  apply Or.inr ∘ Or.inr
  by_cases isSource : index = source
  · subst index;exact ⟨sourceNode,sourceAt⟩
  · change (((slot.after tag).nodes.insert child newNode).insert source _).get index = some staged at stagedAt
    rw [GeneralBorrowFreshLocation.get_other _ source index _ isSource,GeneralBorrowFreshLocation.get_other _ child index _ isChild] at stagedAt
    change (tree.nodes.insert slot.index _).get index = some staged at stagedAt
    rw [GeneralBorrowFreshLocation.get_other _ slot.index index _ isZero] at stagedAt
    exact ⟨staged,stagedAt⟩

private theorem boolAfter_zero_node (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (child source : UniIndex) (sourceNode newNode : TreeNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (vacant : (slot.after tag).nodes.get child = none) (sourceAt : tree.nodes.get source = some sourceNode) :
    ∃ next,(boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get slot.index = some next ∧
      next.tag = tag ∧ next.defaultInitialPermission = .ReservedFrz false ∧ next.children = #[] ∧ next.isExposed = false := by
  let zero := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
  let stage := boolStage tree slot tag child source sourceNode newNode mapping locations
  have zeroAt : (slot.after tag).nodes.get slot.index = some zero := GeneralBorrowFreshLocation.get_same _ _ _
  have notChild : slot.index ≠ child := by intro same;rw [same,vacant] at zeroAt;cases zeroAt
  have notSource : slot.index ≠ source := by intro same;rw [←same,slot.vacant] at sourceAt;cases sourceAt
  have stagedAt : stage.nodes.get slot.index = some zero := by
    change (((slot.after tag).nodes.insert child newNode).insert source _).get slot.index = some zero
    rw [GeneralBorrowFreshLocation.get_other _ source slot.index _ notSource,
      GeneralBorrowFreshLocation.get_other _ child slot.index _ notChild]
    exact zeroAt
  obtain ⟨next,nextAt,tagEq,_,children,permission,exposure⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields stage source .None slot.index zero stagedAt
  exact ⟨next,nextAt,tagEq,permission,children,exposure⟩

/-- Initial full raw rights for the real Bool child under the partial logical
completion. This does not assert a completed origin for the zero root. -/
private theorem boolAfter_authority (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (complete : Completes tree completion)
    (child source : UniIndex) (sourceNode newNode : TreeNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (vacant : (slot.after tag).nodes.get child = none) (sourceAt : tree.nodes.get source = some sourceNode)
    (current : LocationTree) (protections : ProtectedTags)
    (rights : ZeroRights tree slot tag completion protections source current)
    (normal : DuplicatePrefixBorrowAuthorization.Normal (boolAfter tree slot tag child source sourceNode newNode mapping locations) current protections child) :
    Authority (boolAfter tree slot tag child source sourceNode newNode mapping locations)
      (S05ConcreteProtectedChildCompletion.extend completion child source) protections child current := by
  let after := boolAfter tree slot tag child source sourceNode newNode mapping locations
  have ancestry := boolChild_ancestry tree slot tag completion complete child source vacant sourceNode sourceAt
  intro index node present
  rcases boolAfter_cases tree slot tag child source sourceNode newNode mapping locations sourceAt index node present with same | same | original
  · subst index
    obtain ⟨state,stored,compatible⟩ := normal.permissions .Write child.toNat normal.component.anchor
      (GeneralBorrowNodeUpdate.lookup_valid after.nodes child node present)
    have actualState := GeneralBorrowProjection.projection_state after current protections child.toNat child node
      (GeneralBorrowProjection.index_self child) rfl present
    have same : state = RawState current child node := Option.some.inj (stored.symm.trans actualState)
    subst state
    rw [GeneralBorrowNormalPermissionMetadata.held after current protections child node present,
      GeneralBorrowSharedNormalRelations.child_self] at compatible
    exact ⟨fun _ => compatible,fun outside => False.elim (outside (.refl child))⟩
  · subst index
    obtain ⟨next,nextAt,nextTag,nextPermission,_,_⟩ := boolAfter_zero_node tree slot tag child source sourceNode newNode mapping locations vacant sourceAt
    have same : next = node := Option.some.inj (nextAt.symm.trans present)
    subst next
    let zero := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
    have scalar := zero_authority_state _ _ (zero_effective_shape current current zero node rfl nextPermission slot.index) (protections.contains tag)
    rw [nextTag]
    exact ⟨fun below => False.elim (ancestry.2 below),fun _ => scalar.2.mpr rights.2⟩
  · obtain ⟨original,originalAt⟩ := original
    obtain ⟨next,nextAt,nextTag,_,nextPermission,_⟩ := boolAfter_old_node tree slot tag child source sourceNode newNode mapping locations vacant sourceAt index original originalAt
    have same : next = node := Option.some.inj (nextAt.symm.trans present)
    subst next
    have scalar := zero_authority_state _ _ (zero_effective_shape current current original node rfl nextPermission index) (protections.contains original.tag)
    rw [nextTag]
    have equivalent := ancestry.1 index original originalAt
    exact ⟨fun below => scalar.1.mpr ((rights.1 index original originalAt).1 (equivalent.mp below)),
      fun outside => scalar.2.mpr ((rights.1 index original originalAt).2 (fun below => outside (equivalent.mpr below)))⟩


private theorem boolAfter_rights_of_authority (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (complete : Completes tree completion)
    (child source : UniIndex) (sourceNode newNode : TreeNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (vacant : (slot.after tag).nodes.get child = none) (sourceAt : tree.nodes.get source = some sourceNode)
    (current : LocationTree) (protections : ProtectedTags)
    (authority : Authority (boolAfter tree slot tag child source sourceNode newNode mapping locations)
      (S05ConcreteProtectedChildCompletion.extend completion child source) protections child current) :
    ZeroRights tree slot tag completion protections source current := by
  have ancestry := boolChild_ancestry tree slot tag completion complete child source vacant sourceNode sourceAt
  constructor
  · intro index original originalAt
    obtain ⟨next,nextAt,nextTag,_,permission,_⟩ := boolAfter_old_node tree slot tag child source sourceNode newNode mapping locations vacant sourceAt index original originalAt
    have scalar := zero_authority_state _ _ (zero_effective_shape current current original next rfl permission index) (protections.contains original.tag)
    have rights := authority index next nextAt
    rw [nextTag] at rights
    have equivalent := ancestry.1 index original originalAt
    exact ⟨fun below => scalar.1.mp (rights.1 (equivalent.mpr below)),
      fun outside => scalar.2.mp (rights.2 (fun below => outside (equivalent.mp below)))⟩
  · obtain ⟨next,nextAt,nextTag,permission,_,_⟩ := boolAfter_zero_node tree slot tag child source sourceNode newNode mapping locations vacant sourceAt
    let zero := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
    have scalar := zero_authority_state _ _ (zero_effective_shape current current zero next rfl permission slot.index) (protections.contains tag)
    have rights := (authority slot.index next nextAt).2 ancestry.2
    rw [nextTag] at rights
    exact scalar.2.mp rights

private theorem boolAfter_rights_of_parent_authority (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (complete : Completes tree completion)
    (child source : UniIndex) (sourceNode newNode : TreeNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (vacant : (slot.after tag).nodes.get child = none) (sourceAt : tree.nodes.get source = some sourceNode)
    (current : LocationTree) (protections : ProtectedTags)
    (authority : Authority (boolAfter tree slot tag child source sourceNode newNode mapping locations)
      (S05ConcreteProtectedChildCompletion.extend completion child source) protections source current) :
    ZeroRights tree slot tag completion protections source current := by
  have ancestry := boolChild_ancestry tree slot tag completion complete child source vacant sourceNode sourceAt
  have oldVacant : tree.nodes.get child = none := by
    cases present : tree.nodes.get child with
    | none => rfl
    | some node =>
      have nextAt := S04ZeroRootObserverNormal.old_node tree slot tag child node present
      change (slot.after tag).nodes.get child = some node at nextAt
      rw [vacant] at nextAt;cases nextAt
  have parentEquiv (index : UniIndex) : Below (S05ConcreteProtectedChildCompletion.extend completion child source) index source ↔ Below completion index source :=
    S05ConcreteProtectedChildCompletion.old_ancestry_iff tree completion complete child source oldVacant ⟨sourceNode,sourceAt⟩
  constructor
  · intro index original originalAt
    obtain ⟨next,nextAt,nextTag,_,permission,_⟩ := boolAfter_old_node tree slot tag child source sourceNode newNode mapping locations vacant sourceAt index original originalAt
    have scalar := zero_authority_state _ _ (zero_effective_shape current current original next rfl permission index) (protections.contains original.tag)
    have rights := authority index next nextAt
    rw [nextTag] at rights
    have equivalent := parentEquiv index
    exact ⟨fun below => scalar.1.mp (rights.1 (equivalent.mpr below)),
      fun outside => scalar.2.mp (rights.2 (fun below => outside (equivalent.mp below)))⟩
  · obtain ⟨next,nextAt,nextTag,permission,_,_⟩ := boolAfter_zero_node tree slot tag child source sourceNode newNode mapping locations vacant sourceAt
    let zero := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
    have scalar := zero_authority_state _ _ (zero_effective_shape current current zero next rfl permission slot.index) (protections.contains tag)
    have rights := (authority slot.index next nextAt).2
      (fun below => ancestry.2 (.step (S05ConcreteProtectedChildCompletion.child_edge completion child source) below))
    rw [nextTag] at rights
    exact scalar.2.mp rights

/-- Per-row visitors read the actual node/cache metadata and explicit row;
changing only the allocation's surrounding location map does not rerun SIFA. -/
private theorem source_access_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (row : LocationTree) (source : Option UniIndex) (kind : AccessKind) (held : ProtectedTags)
    (mode : ChildrenVisitMode) (range : ByteRange) :
    source_tree_access_at {tree with locations := locations} row source kind held mode range =
      source_tree_access_at tree row source kind held mode range := by rfl


private theorem boolAfter_old_path_back (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (complete : Completes tree completion)
    (child source : UniIndex) (sourceNode newNode : TreeNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (vacant : (slot.after tag).nodes.get child = none) (sourceAt : tree.nodes.get source = some sourceNode)
    {first last : UniIndex} (path : GeneralBorrowExposedNonleafPrimaryPath.Path
      (boolAfter tree slot tag child source sourceNode newNode mapping locations) first last)
    (original : TreeNode) (originalAt : tree.nodes.get last = some original) :
    GeneralBorrowExposedNonleafPrimaryPath.Path tree first last := by
  induction path generalizing original with
  | refl node present => exact .refl _ original originalAt
  | @step parent target earlier node present edge ih =>
    obtain ⟨next,nextAt,_,parentEq,_⟩ := boolAfter_old_node tree slot tag child source sourceNode newNode mapping locations vacant sourceAt target original originalAt
    have same : next = node := Option.some.inj (nextAt.symm.trans present)
    subst next
    have originalEdge : original.parent = some parent := parentEq.symm.trans edge
    have logicalEdge := (complete.2.2.2.2.1 target original originalAt).2.2.1 parent originalEdge
    obtain ⟨parentNode,parentAt⟩ := (complete.2.2.2.2.2.2 target parent logicalEdge).2.1
    exact .step (ih parentNode parentAt) original originalAt originalEdge

private theorem boolChild_path_iff (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (complete : Completes tree completion)
    (child source : UniIndex) (sourceNode newNode : TreeNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (vacant : (slot.after tag).nodes.get child = none) (sourceAt : tree.nodes.get source = some sourceNode)
    (parent : newNode.parent = some source) (query : UniIndex) :
    GeneralBorrowExposedNonleafPrimaryPath.Path (boolAfter tree slot tag child source sourceNode newNode mapping locations) query child ↔
      query = child ∨ GeneralBorrowExposedNonleafPrimaryPath.Path tree query source := by
  let after := boolAfter tree slot tag child source sourceNode newNode mapping locations
  obtain ⟨actual,actualAt,_,actualParent,_,_,_⟩ := boolAfter_child_node tree slot tag child source sourceNode newNode mapping locations vacant sourceAt
  have actualEdge : actual.parent = some source := actualParent.trans parent
  constructor
  · intro path
    cases path with
    | refl => exact Or.inl rfl
    | @step predecessor _ earlier node present edge =>
      have same : node = actual := Option.some.inj (present.symm.trans actualAt)
      subst node
      have equal : predecessor = source := Option.some.inj (edge.symm.trans actualEdge)
      subst predecessor
      exact Or.inr (boolAfter_old_path_back tree slot tag completion complete child source sourceNode newNode mapping locations vacant sourceAt earlier sourceNode sourceAt)
  · rintro (same | path)
    · subst query;exact .refl child actual actualAt
    · have extended : GeneralBorrowExposedNonleafPrimaryPath.Path after query source := by
        apply GeneralBorrowSharedAuthorizationGeometry.path_extension tree after _ query source path
        intro index node present
        obtain ⟨next,nextAt,_,nextParent,_⟩ := boolAfter_old_node tree slot tag child source sourceNode newNode mapping locations vacant sourceAt index node present
        exact ⟨next,nextAt,nextParent⟩
      exact .step extended actual actualAt actualEdge


/-- On the selected actual physical component, the partial logical ancestry
has exactly the real Boolchild's Local/Foreign classification. -/
private theorem boolChild_physical (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (complete : Completes tree completion)
    (child source : UniIndex) (sourceNode newNode : TreeNode) (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (vacant : (slot.after tag).nodes.get child = none) (sourceAt : tree.nodes.get source = some sourceNode)
    (parent : newNode.parent = some source) (position : Nat) (root : UniIndex) (rootNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root source)
    (query : UniIndex) (node : TreeNode)
    (present : (boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get query = some node)
    (rootQuery : GeneralBorrowExposedNonleafPrimaryPath.Path
      (boolAfter tree slot tag child source sourceNode newNode mapping locations) root query) :
    Below (S05ConcreteProtectedChildCompletion.extend completion child source) query child ↔
      GeneralBorrowExposedNonleafPrimaryPath.Path (boolAfter tree slot tag child source sourceNode newNode mapping locations) query child := by
  have ancestry := boolChild_ancestry tree slot tag completion complete child source vacant sourceNode sourceAt
  have paths := boolChild_path_iff tree slot tag completion complete child source sourceNode newNode mapping locations vacant sourceAt parent query
  rcases boolAfter_cases tree slot tag child source sourceNode newNode mapping locations sourceAt query node present with same | same | original
  · subst query
    exact ⟨fun _ => paths.mpr (Or.inl rfl),fun _ => .refl child⟩
  · subst query
    constructor
    · intro below;exact False.elim (ancestry.2 below)
    · intro path
      rcases paths.mp path with same | old
      · have actual : (slot.after tag).nodes.get slot.index = some (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) := GeneralBorrowFreshLocation.get_same _ _ _
        rw [same,vacant] at actual;cases actual
      · have firstLive : ∀ {first last : UniIndex},GeneralBorrowExposedNonleafPrimaryPath.Path tree first last → ∃ node,tree.nodes.get first = some node := by
          intro first last walk
          induction walk with
          | refl node present => exact ⟨node,present⟩
          | step earlier _ _ _ ih => exact ih
        obtain ⟨original,originalAt⟩ := firstLive old
        rw [slot.vacant] at originalAt;cases originalAt
  · obtain ⟨original,originalAt⟩ := original
    have notChild : query ≠ child := by
      intro same
      have actual := S04ZeroRootObserverNormal.old_node tree slot tag query original originalAt
      change (slot.after tag).nodes.get query = some original at actual
      rw [same,vacant] at actual;cases actual
    have oldRootQuery := boolAfter_old_path_back tree slot tag completion complete child source sourceNode newNode mapping locations vacant sourceAt rootQuery original originalAt
    obtain ⟨actualRoot,actualRootAt,parentless⟩ := complete.2.2.2.1 position root rootSlot
    have same : actualRoot = rootNode := Option.some.inj (actualRootAt.symm.trans rootPresent)
    subst actualRoot
    have physical := CompletedBorrowPhysicalSource.same_root_ancestor_iff complete rootPresent parentless originalAt oldRootQuery sourcePath
    have pathEq : GeneralBorrowExposedNonleafPrimaryPath.Path (boolAfter tree slot tag child source sourceNode newNode mapping locations) query child ↔
        GeneralBorrowExposedNonleafPrimaryPath.Path tree query source := by simpa only [notChild,false_or] using paths
    exact (ancestry.1 query original originalAt).trans (physical.trans pathEq.symm)


private theorem bool_constructor_representation (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (before : BorrowTree) (global : GlobalState) (beforeEq : before = {(slot.after tag) with locations := before.locations})
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts before global)
    (source : UniIndex) (sourceNode : TreeNode) (sourceAt : tree.nodes.get source = some sourceNode)
    (newTag : BorTag) (tagged : before.indexOfTag sourceNode.tag = some source)
    (fresh : GeneralBorrowTagMap.Fresh before.tagMapping newTag) (room : before.nodes.size+1 ≤ 4294967295)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ before.locations.size.bytes.toNat) :
    let actual := before.newChild (Size.ofBytes offset) (.concrete sourceNode.tag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    ∃ child mapping locations,(slot.after tag).nodes.get child = none ∧
      actual.tree = boolAfter tree slot tag child source sourceNode (GeneralBorrowFreshChild.child newTag source) mapping locations ∧
      actual.tree.indexOfTag newTag = some child := by
  have beforeNodes : before.nodes = (slot.after tag).nodes := by rw [beforeEq]
  have beforeRoots : before.roots = (slot.after tag).roots := by rw [beforeEq]
  have present : before.nodeAt source = some sourceNode := by
    change before.nodes.get source = some sourceNode
    rw [beforeNodes]
    exact S04ZeroRootObserverNormal.old_node tree slot tag source sourceNode sourceAt
  let rank := GeneralBorrowStructuralHistoryMutable.depth before runtime.formed.toState
  let nextSlot := GeneralBorrowStructuralHistoryMutable.slot before runtime.formed.toState source sourceNode present room
  cases nextSlot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨before,rank,runtime.formed.children,runtime.formed.covered,sourceNode.tag,newTag,source,sourceNode,tagged,present,fresh,
        noFree,aligned,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildMutable.append input
    have atEnd : (GeneralBorrowFreshMetadataChildMutable.index input).toNat = before.nodes.data.size := GeneralBorrowFreshMetadataChildMutable.at_end input
    have vacant : before.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by
      simp only [UniValMap.get,atEnd,Array.getElem?_eq_none (Nat.le_refl _)]
    have stageEq : GeneralBorrowFreshMetadataChildMutable.stage input =
        boolStage tree slot tag (GeneralBorrowFreshMetadataChildMutable.index input) source sourceNode (GeneralBorrowFreshChild.child newTag source)
          (GeneralBorrowFreshMetadataChildMutable.mapping input) (GeneralBorrowFreshMetadataChildMutable.locations input) := by
      simp only [GeneralBorrowFreshMetadataChildMutable.stage,GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,input,boolStage,
        beforeNodes,beforeRoots]
    refine ⟨GeneralBorrowFreshMetadataChildMutable.index input,GeneralBorrowFreshMetadataChildMutable.mapping input,
      GeneralBorrowFreshMetadataChildMutable.locations input,?_,?_,data.freshLookup⟩
    · rw [←beforeNodes]
      exact vacant
    · exact (GeneralBorrowFreshMetadataChildMutable.tree_eq input).trans (congrArg (fun stage => (sourceUpdateSifa stage source .None).1) stageEq)
  | reuse index available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨before,rank,runtime.formed.children,runtime.formed.covered,sourceNode.tag,newTag,source,sourceNode,tagged,present,fresh,
        index,available,bounded,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have data := GeneralBorrowFreshMetadataChildMutableReuse.reuse input
    have stageEq : GeneralBorrowFreshMetadataChildMutableReuse.stage input =
        boolStage tree slot tag index source sourceNode (GeneralBorrowFreshChild.child newTag source)
          (GeneralBorrowFreshMetadataChildMutableReuse.mapping input) (GeneralBorrowFreshMetadataChildMutableReuse.locations input) := by
      simp only [GeneralBorrowFreshMetadataChildMutableReuse.stage,GeneralBorrowFreshMetadataChildMutableReuse.index,
        GeneralBorrowFreshMetadataChildAttach.staged,GeneralBorrowFreshGraph.attached,input,boolStage,beforeNodes,beforeRoots]
    refine ⟨index,GeneralBorrowFreshMetadataChildMutableReuse.mapping input,GeneralBorrowFreshMetadataChildMutableReuse.locations input,?_,?_,data.freshLookup⟩
    · rw [←beforeNodes]
      exact vacant
    · exact (GeneralBorrowFreshMetadataChildMutableReuse.tree_eq input).trans (congrArg (fun stage => (sourceUpdateSifa stage source .None).1) stageEq)

private theorem bool_attached_size (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (child source : UniIndex) (sourceNode newNode : TreeNode)
    (vacant : (slot.after tag).nodes.get child = none) (sourceAt : tree.nodes.get source = some sourceNode) :
    (slot.after tag).nodes.size ≤ (attachedNodes (slot.after tag).nodes child source sourceNode newNode).size := by
  have parentAt : (slot.after tag).nodes.get source = some sourceNode := S04ZeroRootObserverNormal.old_node tree slot tag source sourceNode sourceAt
  have different : source ≠ child := by intro same;rw [same,vacant] at parentAt;cases parentAt
  have parentInserted : ((slot.after tag).nodes.insert child newNode).get source = some sourceNode :=
    (GeneralBorrowFreshLocation.get_other _ child source _ different).trans parentAt
  unfold attachedNodes
  rw [insert_existing_size _ source sourceNode _ parentInserted]
  simp only [UniValMap.insert,Id.run,pure]
  split <;> simp only [UniValMap.size,Array.size_set,UniValMap.extendTo,Array.size_append,Array.size_replicate] <;> omega


private theorem zero_sifa_write_callback (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (protections : ProtectedTags) (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree selected source)
    (child : UniIndex) (newNode : TreeNode) (vacant : (slot.after tag).nodes.get child = none) (hidden : newNode.isExposed = false)
    (size : (slot.after tag).nodes.size ≤ (attachedNodes (slot.after tag).nodes child source sourceNode newNode).size)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (formed : GeneralBorrowStructuralHistoryState.GraphState (boolAfter tree slot tag child source sourceNode newNode mapping locations))
    (nextOrder : ParentTagOrder (boolAfter tree slot tag child source sourceNode newNode mapping locations))
    (initial current : LocationTree) (initialRights : ZeroRights tree slot tag completion protections source initial)
    (coherent : LocationCoherent (boolAfter tree slot tag child source sourceNode newNode mapping locations) current protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile (boolAfter tree slot tag child source sourceNode newNode mapping locations) current protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible (boolAfter tree slot tag child source sourceNode newNode mapping locations) current)
    (short : (boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.size < 65536)
    (position : Nat) (root : UniIndex) (rootAt : (boolAfter tree slot tag child source sourceNode newNode mapping locations).roots[position]? = some root)
    (different : root ≠ selected)
    (frame : ∀ index node,(boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get index = some node →
      GeneralBorrowExposedNonleafPrimaryPath.Path (boolAfter tree slot tag child source sourceNode newNode mapping locations) root index →
      current.perms.get index = initial.perms.get index) :
    let after := boolAfter tree slot tag child source sourceNode newNode mapping locations
    let result := after.performWildcardAccessAt current root (some selectedNode.tag) .Write protections (position != 0)
    result.status = .Completed ∧ LocationCoherent after result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile after result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible after result.location ∧
      ∀ query, ¬GeneralBorrowExposedNonleafPrimaryPath.Path after root query → result.location.perms.get query = current.perms.get query := by
  let stage := boolStage tree slot tag child source sourceNode newNode mapping locations
  let after := boolAfter tree slot tag child source sourceNode newNode mapping locations
  have shape : treeShape after = treeShape stage := GeneralBorrowSifaView.preserves stage source .None
  have stageFormed := GeneralBorrowStructuralHistoryState.graph_shape after stage shape.symm formed
  obtain ⟨stageDepth⟩ := stageFormed.depth
  obtain ⟨afterDepth⟩ := formed.depth
  have parentBefore := S04ZeroRootObserverNormal.old_node tree slot tag source sourceNode sourcePresent
  let parentNode := {sourceNode with children := sourceNode.children.push child}
  have parentAt : stage.nodes.get source = some parentNode := GeneralBorrowFreshLocation.get_same _ _ _
  have parents := GeneralBorrowSharedCallbacksAttach.parents (slot.after tag) child source sourceNode newNode vacant parentBefore
  have sourceStagePath : GeneralBorrowExposedNonleafPrimaryPath.Path stage selected source := by
    apply GeneralBorrowSharedAuthorizationGeometry.path_extension (slot.after tag) stage parents selected source
    apply GeneralBorrowSharedAuthorizationGeometry.path_extension tree (slot.after tag) _ selected source sourcePath
    intro query node present
    exact ⟨node,S04ZeroRootObserverNormal.old_node tree slot tag query node present,rfl⟩
  have roots : after.roots = stage.roots := GeneralBorrowFreshMetadata.roots stage after shape
  have rootStageAt : stage.roots[position]? = some root := by rw [←roots];exact rootAt
  have selectedBound := (Array.getElem?_eq_some_iff.mp selectedSlot).1
  have selectedStageAt : stage.roots[selectedPosition]? = some selected := by
    change (tree.roots.push slot.index)[selectedPosition]? = some selected
    simpa only [Array.getElem?_push,ite_eq_right (Nat.ne_of_lt selectedBound)] using selectedSlot
  have outside (query : UniIndex) (path : GeneralBorrowExposedNonleafPrimaryPath.Path stage root query) :
      ¬GeneralBorrowExposedNonleafPrimaryPath.Path stage query source := by
    intro tail
    have full := GeneralBorrowSharedAuthorizationGeometry.path_trans path tail
    obtain ⟨rootNode,rootPresent,rootParentless⟩ := stageFormed.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootStageAt))
    obtain ⟨selectedActual,selectedAt,selectedParentless⟩ := stageFormed.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? selectedStageAt))
    exact different (CompletedBorrowAncestry.physical_roots_unique rootPresent rootParentless selectedAt selectedParentless full sourceStagePath)
  have extend (first last : UniIndex) (path : GeneralBorrowExposedNonleafPrimaryPath.Path stage first last) :
      GeneralBorrowExposedNonleafPrimaryPath.Path after first last := by
    apply GeneralBorrowSharedAuthorizationGeometry.path_extension stage after _ first last path
    intro index node present
    obtain ⟨next,found,_,parent,_⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields stage source .None index node present
    exact ⟨next,found,parent⟩
  have nodeFrame (index : UniIndex) (path : GeneralBorrowExposedNonleafPrimaryPath.Path stage root index) :
      after.nodes.get index = stage.nodes.get index :=
    congrArg Prod.fst (GeneralBorrowSifaOutsidePath.frame stage stageDepth source parentNode parentAt index (outside index path) .None)
  have currentFrame : ∀ index node,stage.nodes.get index = some node → GeneralBorrowExposedNonleafPrimaryPath.Path stage root index →
      current.perms.get index = initial.perms.get index := by
    intro index node present path
    exact frame index node ((nodeFrame index path).trans present) (extend root index path)
  have consistency : ∀ index node,stage.nodes.get index = some node → GeneralBorrowExposedNonleafPrimaryPath.Path stage root index →
      GeneralBorrowSifaPermissionConsistency.Consistent ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) := by
    intro index node present path
    exact profile.present index node ((nodeFrame index path).trans present)
  have auth := zero_write_authorization tree slot tag completion protections complete depth order selectedPosition selected source selectedNode sourceNode
    selectedSlot selectedPresent sourcePresent sourcePath child newNode vacant hidden size mapping locations stageDepth initial current initialRights
    position root rootStageAt different currentFrame consistency
  let support : UniIndex → Prop := fun query => if position < tree.roots.size then GeneralBorrowExposedNonleafPrimaryPath.Path tree root query else query = slot.index
  have supportPath (query : UniIndex) (included : support query) : GeneralBorrowExposedNonleafPrimaryPath.Path stage root query := by
    obtain ⟨node,present⟩ := auth.present query included
    exact GeneralBorrowWildcardControlWitness.path_of_covers stage stageDepth root query node present (auth.covers query included)
  have afterAuth := CurrentCallEmptyEntrySifaWrite.current_row stage stageDepth source parentNode parentAt current protections root position
    (some selectedNode.tag) support auth (fun query included => outside query (supportPath query included))
  obtain ⟨done,cache,sifa,gp,outsideSupport⟩ := CurrentCallEmptyEntryZeroRootQueries.write_of_authorization after current protections formed nextOrder
    afterDepth root position (some selectedNode.tag) support afterAuth coherent short profile possible
  refine ⟨done,cache,sifa,gp,?_⟩
  intro query notPath
  exact outsideSupport query (fun included => notPath (extend root query (supportPath query included)))

/-- The repaired per-root data consumed by the retained actual Write kernel. -/
structure WriteQueries (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (source root : UniIndex) (position : Nat) (maximum : Option BorTag) (current : LocationTree) where
  support : UniIndex → Prop
  authorization : DuplicatePrefixResidualWriteRepaired.Authorization tree current protections root position maximum .Write support
  path : ∀ query,support query → GeneralBorrowExposedNonleafPrimaryPath.Path tree root query
  classification : ∀ removed,DuplicatePrefixResidualSupportAuthorization.Removal tree current protections maximum .Write removed →
    ∀ query node,support query → tree.nodes.get query=some node →
    let classified := DuplicatePrefixResidualSupportAuthorization.residualRelation tree current protections root query node maximum .Write position removed
    (Below completion query source → classified=some .LocalAccess ∨ classified=some .EitherAccess) ∧
    (¬Below completion query source → classified=some .ForeignAccess ∨ classified=some .EitherAccess)

private def write_queries_locations (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags)
    (source root : UniIndex) (position : Nat) (maximum : Option BorTag) (current : LocationTree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (locations : DedupRangeMap LocationTree)
    (queries : WriteQueries tree completion protections source root position maximum current) :
    WriteQueries {tree with locations:=locations} completion protections source root position maximum current := by
  obtain ⟨auth,classification⟩ := CurrentCallEmptyEntryRepairedMetadata.queries tree {tree with locations:=locations} current current protections
    depth depth (Nat.le_refl _) (by intro index node present;exact ⟨node,present,rfl,rfl,rfl,rfl⟩)
    (by intro index node present _;exact ⟨node,present⟩) root position maximum .Write queries.support queries.authorization
    (by intro;intro;rfl) (by intro;intro;rfl) completion completion source queries.classification (by intro;intro;exact Iff.rfl)
  refine ⟨queries.support,auth,?_,classification⟩
  intro query included
  apply GeneralBorrowSharedAuthorizationGeometry.path_extension tree {tree with locations:=locations} _ root query (queries.path query included)
  intro index node present
  exact ⟨node,present,rfl⟩

/-- Actual orphan-component geometry retained from the bounded empty constructor. -/
structure OrphanWriteFactory (tree : BorrowTree) (completion : Completion) (protections : ProtectedTags) (source : UniIndex) (qTag : BorTag) where
  selectedPosition : Nat
  selected : UniIndex
  selectedNode : TreeNode
  selectedSlot : tree.roots[selectedPosition]?=some selected
  selectedAt : tree.nodeAt selected=some selectedNode
  selectedPath : GeneralBorrowExposedNonleafPrimaryPath.Path tree selected source
  orphan : UniIndex
  orphanPosition : Nat
  orphanMapped : tree.indexOfTag qTag=some orphan
  orphanSlot : tree.roots[orphanPosition]?=some orphan
  later : 0<orphanPosition
  notBelow : ¬Below completion orphan source
  different : selected≠orphan
  distinct : tree.roots.toList.Nodup
  selectedClassification : ∀ query node,tree.nodes.get query=some node →
    GeneralBorrowExposedNonleafPrimaryPath.Path tree selected query →
    (Below completion query source ↔ GeneralBorrowExposedNonleafPrimaryPath.Path tree query source)
  callbacks : ∀ current : LocationTree,Authority tree completion protections source current →
    ∀ (position : Nat) (root : UniIndex),tree.roots[position]?=some root → root≠selected →
    (∀ index node,tree.nodes.get index=some node → GeneralBorrowExposedNonleafPrimaryPath.Path tree root index →
      GeneralBorrowSifaPermissionConsistency.Consistent ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) →
    Nonempty (WriteQueries tree completion protections source root position (some selectedNode.tag) current)

private theorem zero_sifa_write_queries (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (protections : ProtectedTags) (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree selected source)
    (child : UniIndex) (newNode : TreeNode) (vacant : (slot.after tag).nodes.get child = none) (hidden : newNode.isExposed = false)
    (size : (slot.after tag).nodes.size ≤ (attachedNodes (slot.after tag).nodes child source sourceNode newNode).size)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (formed : GeneralBorrowStructuralHistoryState.GraphState (boolAfter tree slot tag child source sourceNode newNode mapping locations))
    (initial current : LocationTree) (initialRights : ZeroRights tree slot tag completion protections source initial)
    (currentAuthority : Authority (boolAfter tree slot tag child source sourceNode newNode mapping locations)
      (S05ConcreteProtectedChildCompletion.extend completion child source) protections child current)
    (position : Nat) (root : UniIndex) (rootAt : (boolAfter tree slot tag child source sourceNode newNode mapping locations).roots[position]? = some root)
    (different : root ≠ selected)
    (frame : ∀ index node,(boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get index = some node →
      GeneralBorrowExposedNonleafPrimaryPath.Path (boolAfter tree slot tag child source sourceNode newNode mapping locations) root index →
      current.perms.get index = initial.perms.get index)
    (currentConsistent : ∀ index node,(boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get index=some node →
      GeneralBorrowExposedNonleafPrimaryPath.Path (boolAfter tree slot tag child source sourceNode newNode mapping locations) root index →
      GeneralBorrowSifaPermissionConsistency.Consistent ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag)) :
    Nonempty (WriteQueries (boolAfter tree slot tag child source sourceNode newNode mapping locations)
      (S05ConcreteProtectedChildCompletion.extend completion child source) protections child root position (some selectedNode.tag) current) := by
  let stage := boolStage tree slot tag child source sourceNode newNode mapping locations
  let after := boolAfter tree slot tag child source sourceNode newNode mapping locations
  have shape : treeShape after = treeShape stage := GeneralBorrowSifaView.preserves stage source .None
  have stageFormed := GeneralBorrowStructuralHistoryState.graph_shape after stage shape.symm formed
  obtain ⟨stageDepth⟩ := stageFormed.depth
  obtain ⟨afterDepth⟩ := formed.depth
  have parentBefore := S04ZeroRootObserverNormal.old_node tree slot tag source sourceNode sourcePresent
  let parentNode := {sourceNode with children := sourceNode.children.push child}
  have parentAt : stage.nodes.get source = some parentNode := GeneralBorrowFreshLocation.get_same _ _ _
  have parents := GeneralBorrowSharedCallbacksAttach.parents (slot.after tag) child source sourceNode newNode vacant parentBefore
  have sourceStagePath : GeneralBorrowExposedNonleafPrimaryPath.Path stage selected source := by
    apply GeneralBorrowSharedAuthorizationGeometry.path_extension (slot.after tag) stage parents selected source
    apply GeneralBorrowSharedAuthorizationGeometry.path_extension tree (slot.after tag) _ selected source sourcePath
    intro query node present
    exact ⟨node,S04ZeroRootObserverNormal.old_node tree slot tag query node present,rfl⟩
  have roots : after.roots = stage.roots := GeneralBorrowFreshMetadata.roots stage after shape
  have rootStageAt : stage.roots[position]? = some root := by rw [←roots];exact rootAt
  have selectedBound := (Array.getElem?_eq_some_iff.mp selectedSlot).1
  have selectedStageAt : stage.roots[selectedPosition]? = some selected := by
    change (tree.roots.push slot.index)[selectedPosition]? = some selected
    simpa only [Array.getElem?_push,ite_eq_right (Nat.ne_of_lt selectedBound)] using selectedSlot
  have outside (query : UniIndex) (path : GeneralBorrowExposedNonleafPrimaryPath.Path stage root query) :
      ¬GeneralBorrowExposedNonleafPrimaryPath.Path stage query source := by
    intro tail
    have full := GeneralBorrowSharedAuthorizationGeometry.path_trans path tail
    obtain ⟨rootNode,rootPresent,rootParentless⟩ := stageFormed.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? rootStageAt))
    obtain ⟨selectedActual,selectedAt,selectedParentless⟩ := stageFormed.rootNodes selected (Array.mem_toList_iff.mpr (Array.mem_of_getElem? selectedStageAt))
    exact different (CompletedBorrowAncestry.physical_roots_unique rootPresent rootParentless selectedAt selectedParentless full sourceStagePath)
  have extend (first last : UniIndex) (path : GeneralBorrowExposedNonleafPrimaryPath.Path stage first last) :
      GeneralBorrowExposedNonleafPrimaryPath.Path after first last := by
    apply GeneralBorrowSharedAuthorizationGeometry.path_extension stage after _ first last path
    intro index node present
    obtain ⟨next,found,_,parent,_⟩ := GeneralBorrowFreshMetadataChildSifa.node_fields stage source .None index node present
    exact ⟨next,found,parent⟩
  have nodeFrame (index : UniIndex) (path : GeneralBorrowExposedNonleafPrimaryPath.Path stage root index) :
      after.nodes.get index = stage.nodes.get index :=
    congrArg Prod.fst (GeneralBorrowSifaOutsidePath.frame stage stageDepth source parentNode parentAt index (outside index path) .None)
  have currentFrame : ∀ index node,stage.nodes.get index = some node → GeneralBorrowExposedNonleafPrimaryPath.Path stage root index →
      current.perms.get index = initial.perms.get index := by
    intro index node present path
    exact frame index node ((nodeFrame index path).trans present) (extend root index path)
  have consistency : ∀ index node,stage.nodes.get index = some node → GeneralBorrowExposedNonleafPrimaryPath.Path stage root index →
      GeneralBorrowSifaPermissionConsistency.Consistent ((current.perms.get index).getD node.defaultLocationState) (protections.contains node.tag) := by
    intro index node present path
    exact currentConsistent index node ((nodeFrame index path).trans present) (extend root index path)
  have auth := zero_write_authorization tree slot tag completion protections complete depth order selectedPosition selected source selectedNode sourceNode
    selectedSlot selectedPresent sourcePresent sourcePath child newNode vacant hidden size mapping locations stageDepth initial current initialRights
    position root rootStageAt different currentFrame consistency
  let support : UniIndex → Prop := fun query => if position < tree.roots.size then GeneralBorrowExposedNonleafPrimaryPath.Path tree root query else query = slot.index
  have supportPath (query : UniIndex) (included : support query) : GeneralBorrowExposedNonleafPrimaryPath.Path stage root query := by
    obtain ⟨node,present⟩ := auth.present query included
    exact GeneralBorrowWildcardControlWitness.path_of_covers stage stageDepth root query node present (auth.covers query included)
  have afterAuth := CurrentCallEmptyEntrySifaWrite.current_row stage stageDepth source parentNode parentAt current protections root position
    (some selectedNode.tag) support auth (fun query included => outside query (supportPath query included))
  have ancestry := boolChild_ancestry tree slot tag completion complete child source vacant sourceNode sourcePresent
  have oldPositionFrame (oldPosition : position < tree.roots.size) (query : UniIndex)
      (node : TreeNode) (present : tree.nodes.get query = some node)
      (path : GeneralBorrowExposedNonleafPrimaryPath.Path tree root query) : after.nodes.get query = some node := by
    have included : support query := by simpa only [support,ite_eq_left oldPosition] using path
    have stagePath := supportPath query included
    have notChild : query ≠ child := by
      intro same
      have nextAt := S04ZeroRootObserverNormal.old_node tree slot tag query node present
      change (slot.after tag).nodes.get query = some node at nextAt
      rw [same,vacant] at nextAt;cases nextAt
    have notSource : query ≠ source := by
      intro same
      subst query
      exact outside source stagePath (.refl source parentNode parentAt)
    have stageAt : stage.nodes.get query = some node := by
      change (((slot.after tag).nodes.insert child newNode).insert source _).get query = some node
      rw [GeneralBorrowFreshLocation.get_other _ source query _ notSource,GeneralBorrowFreshLocation.get_other _ child query _ notChild]
      exact S04ZeroRootObserverNormal.old_node tree slot tag query node present
    exact (nodeFrame query stagePath).trans stageAt
  have classification : ∀ removed,DuplicatePrefixResidualSupportAuthorization.Removal after current protections (some selectedNode.tag) .Write removed →
      ∀ query node,support query → after.nodes.get query = some node →
      let classified := DuplicatePrefixResidualSupportAuthorization.residualRelation after current protections root query node (some selectedNode.tag) .Write position removed
      (Below (S05ConcreteProtectedChildCompletion.extend completion child source) query child → classified = some .LocalAccess ∨ classified = some .EitherAccess) ∧
      (¬Below (S05ConcreteProtectedChildCompletion.extend completion child source) query child → classified = some .ForeignAccess ∨ classified = some .EitherAccess) := by
    intro removed legal query node included present
    have transported := boolAfter_query tree slot tag depth child source sourceNode newNode mapping locations vacant sourcePresent hidden size
      current protections root query position (some selectedNode.tag) node removed legal
    dsimp only
    rw [transported.2]
    by_cases oldPosition : position < tree.roots.size
    · have path : GeneralBorrowExposedNonleafPrimaryPath.Path tree root query := by
        simpa only [support,ite_eq_left oldPosition] using included
      obtain ⟨original,originalAt⟩ := path.present
      have same : original = node := Option.some.inj ((oldPositionFrame oldPosition query original originalAt path).symm.trans present)
      subst original
      have oldSlot : tree.roots[position]? = some root := by
        change (tree.roots.push slot.index)[position]? = some root at rootStageAt
        simpa only [Array.getElem?_push,ite_eq_right (Nat.ne_of_lt oldPosition)] using rootStageAt
      have localRights : ∀ index found,tree.nodes.get index = some found → GeneralBorrowExposedNonleafPrimaryPath.Path tree root index →
          Below completion index source → LocalWrite ((current.perms.get index).getD found.defaultLocationState) (protections.contains found.tag) := by
        intro index found lookup walk below
        exact (currentAuthority index found (oldPositionFrame oldPosition index found lookup walk)).1
          ((ancestry.1 index found lookup).mpr below)
      have old := S05CompletedWriteAuthorityRetention.query_shape tree completion current protections complete depth order
        position selectedPosition root selected source query node selectedNode oldSlot selectedSlot selectedPresent different sourcePath path originalAt localRights removed transported.1
      have equivalent := ancestry.1 query node originalAt
      exact ⟨fun below => old.1 (equivalent.mp below),fun outside => old.2 (fun below => outside (equivalent.mpr below))⟩
    · have positionEq : position = tree.roots.size := by
        by_cases equal : position = tree.roots.size
        · exact equal
        · change (tree.roots.push slot.index)[position]? = some root at rootStageAt
          simp only [Array.getElem?_push,ite_eq_right equal] at rootStageAt
          rw [Array.getElem?_eq_none (by omega)] at rootStageAt;cases rootStageAt
      subst position
      have rootEq : slot.index = root := by
        change (tree.roots.push slot.index)[tree.roots.size]? = some root at rootStageAt
        simpa only [Array.getElem?_push,↓reduceIte,Option.some.injEq] using rootStageAt
      subst root
      have same : query = slot.index := by simpa only [support,ite_eq_right (Nat.lt_irrefl tree.roots.size)] using included
      subst query
      have relation : DuplicatePrefixResidualSupportAuthorization.residualRelation tree current protections slot.index slot.index node
          (some selectedNode.tag) .Write tree.roots.size removed = some .ForeignAccess := by
        unfold DuplicatePrefixResidualSupportAuthorization.residualRelation
        rw [S04ZeroLeafCallbackData.vacant_count tree depth current protections slot.index slot.vacant .Write removed]
        apply S04ZeroLeafCallbackData.zero_foreign
        have nonempty : 0 < tree.roots.size := by have bound := (Array.getElem?_eq_some_iff.mp selectedSlot).1;omega
        simp only [show (tree.roots.size != 0) = true by simp [Nat.ne_of_gt nonempty],ite_true]
        omega
      exact ⟨fun impossible => False.elim (ancestry.2 impossible),fun _ => Or.inl relation⟩
  exact ⟨⟨support,afterAuth,(fun query included => extend root query (supportPath query included)),classification⟩⟩

private theorem zero_sifa_write_retained_callback (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (protections : ProtectedTags) (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree selected source)
    (child : UniIndex) (newNode : TreeNode) (vacant : (slot.after tag).nodes.get child = none) (hidden : newNode.isExposed = false)
    (size : (slot.after tag).nodes.size ≤ (attachedNodes (slot.after tag).nodes child source sourceNode newNode).size)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (formed : GeneralBorrowStructuralHistoryState.GraphState (boolAfter tree slot tag child source sourceNode newNode mapping locations))
    (nextOrder : ParentTagOrder (boolAfter tree slot tag child source sourceNode newNode mapping locations))
    (initial current : LocationTree) (initialRights : ZeroRights tree slot tag completion protections source initial)
    (coherent : LocationCoherent (boolAfter tree slot tag child source sourceNode newNode mapping locations) current protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile (boolAfter tree slot tag child source sourceNode newNode mapping locations) current protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible (boolAfter tree slot tag child source sourceNode newNode mapping locations) current)
    (currentAuthority : Authority (boolAfter tree slot tag child source sourceNode newNode mapping locations)
      (S05ConcreteProtectedChildCompletion.extend completion child source) protections child current)
    (short : (boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.size < 65536)
    (position : Nat) (root : UniIndex) (rootAt : (boolAfter tree slot tag child source sourceNode newNode mapping locations).roots[position]? = some root)
    (different : root ≠ selected)
    (frame : ∀ index node,(boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get index = some node →
      GeneralBorrowExposedNonleafPrimaryPath.Path (boolAfter tree slot tag child source sourceNode newNode mapping locations) root index →
      current.perms.get index = initial.perms.get index) :
    let after := boolAfter tree slot tag child source sourceNode newNode mapping locations
    let result := after.performWildcardAccessAt current root (some selectedNode.tag) .Write protections (position != 0)
    result.status = .Completed ∧ LocationCoherent after result.location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile after result.location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible after result.location ∧
      (∀ query, ¬GeneralBorrowExposedNonleafPrimaryPath.Path after root query → result.location.perms.get query = current.perms.get query) ∧
      Authority after (S05ConcreteProtectedChildCompletion.extend completion child source) protections child result.location := by
  dsimp only
  let after := boolAfter tree slot tag child source sourceNode newNode mapping locations
  obtain ⟨queries⟩ := zero_sifa_write_queries tree slot tag completion protections complete depth order selectedPosition selected source selectedNode sourceNode
    selectedSlot selectedPresent sourcePresent sourcePath child newNode vacant hidden size mapping locations formed initial current initialRights currentAuthority position root rootAt different frame
    (by intro index node present _;exact profile.present index node present)
  obtain ⟨afterDepth⟩ := formed.depth
  obtain ⟨done,cache,sifa,gp,outsideSupport,rights⟩ := CurrentCallEmptyEntryWriteRetention.root after current protections formed nextOrder
    afterDepth root position (some selectedNode.tag) queries.support queries.authorization coherent short profile possible
    (S05ConcreteProtectedChildCompletion.extend completion child source) child queries.classification currentAuthority
  exact ⟨done,cache,sifa,gp,(fun query notPath => outsideSupport query (fun included => notPath (queries.path query included))),rights⟩

private theorem zero_sifa_child_write_retained (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (protections : ProtectedTags) (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree selected source)
    (child : UniIndex) (newNode : TreeNode) (vacant : (slot.after tag).nodes.get child = none) (hidden : newNode.isExposed = false)
    (newParent : newNode.parent = some source)
    (size : (slot.after tag).nodes.size ≤ (attachedNodes (slot.after tag).nodes child source sourceNode newNode).size)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (formed : GeneralBorrowStructuralHistoryState.GraphState (boolAfter tree slot tag child source sourceNode newNode mapping locations))
    (nextOrder : ParentTagOrder (boolAfter tree slot tag child source sourceNode newNode mapping locations))
    (distinct : (boolAfter tree slot tag child source sourceNode newNode mapping locations).roots.toList.Nodup)
    (selectedAfter childNode : TreeNode)
    (selectedAfterAt : (boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get selected = some selectedAfter)
    (selectedTag : selectedAfter.tag = selectedNode.tag)
    (childAt : (boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get child = some childNode)
    (childPath : GeneralBorrowExposedNonleafPrimaryPath.Path (boolAfter tree slot tag child source sourceNode newNode mapping locations) selected child)
    (initial : LocationTree) (initialRights : ZeroRights tree slot tag completion protections source initial)
    (normal : DuplicatePrefixBorrowAuthorization.Normal (boolAfter tree slot tag child source sourceNode newNode mapping locations) initial protections child)
    (coherent : LocationCoherent (boolAfter tree slot tag child source sourceNode newNode mapping locations) initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile (boolAfter tree slot tag child source sourceNode newNode mapping locations) initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible (boolAfter tree slot tag child source sourceNode newNode mapping locations) initial)
    (short : (boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.size < 65536)
    (mode : ChildrenVisitMode) (range : ByteRange) :
    let after := boolAfter tree slot tag child source sourceNode newNode mapping locations
    let result := source_tree_access_at after initial (some child) .Write protections mode range
    source_access_status result = none ∧ LocationCoherent after (source_access_location result) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile after (source_access_location result) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible after (source_access_location result) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal after (source_access_location result) protections child) ∧
      Authority after (S05ConcreteProtectedChildCompletion.extend completion child source) protections child (source_access_location result) := by
  let stage := boolStage tree slot tag child source sourceNode newNode mapping locations
  let after := boolAfter tree slot tag child source sourceNode newNode mapping locations
  have shape : treeShape after = treeShape stage := GeneralBorrowSifaView.preserves stage source .None
  have roots : after.roots = stage.roots := GeneralBorrowFreshMetadata.roots stage after shape
  have bound := (Array.getElem?_eq_some_iff.mp selectedSlot).1
  have selectedAfterSlot : after.roots[selectedPosition]? = some selected := by
    rw [roots]
    change (tree.roots.push slot.index)[selectedPosition]? = some selected
    simpa only [Array.getElem?_push,ite_eq_right (Nat.ne_of_lt bound)] using selectedSlot
  have initialAuthority := boolAfter_authority tree slot tag completion complete child source sourceNode newNode mapping locations vacant sourcePresent initial protections initialRights normal
  apply CurrentCallEmptyEntryNormalWrite.write_authority after (S05ConcreteProtectedChildCompletion.extend completion child source) initial protections
    formed distinct selectedPosition selected child selectedAfter childNode selectedAfterSlot selectedAfterAt childAt childPath normal initialAuthority
    (fun index node present path => boolChild_physical tree slot tag completion complete child source sourceNode newNode mapping locations
      vacant sourcePresent newParent selectedPosition selected selectedNode selectedSlot selectedPresent sourcePath index node present path)
    coherent profile possible
  intro position root rootAt different current currentAuthority cache sifa gp currentFrame
  have callback := zero_sifa_write_retained_callback tree slot tag completion protections complete depth order selectedPosition selected source selectedNode sourceNode
    selectedSlot selectedPresent sourcePresent sourcePath child newNode vacant hidden size mapping locations formed nextOrder initial current initialRights
    cache sifa gp currentAuthority short position root rootAt different currentFrame
  simpa only [selectedTag] using callback


private theorem zero_sifa_child_write_unique (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (protections : ProtectedTags) (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree selected source)
    (child : UniIndex) (newNode : TreeNode) (vacant : (slot.after tag).nodes.get child = none) (hidden : newNode.isExposed = false)
    (newParent : newNode.parent = some source)
    (size : (slot.after tag).nodes.size ≤ (attachedNodes (slot.after tag).nodes child source sourceNode newNode).size)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (formed : GeneralBorrowStructuralHistoryState.GraphState (boolAfter tree slot tag child source sourceNode newNode mapping locations))
    (nextOrder : ParentTagOrder (boolAfter tree slot tag child source sourceNode newNode mapping locations))
    (distinct : (boolAfter tree slot tag child source sourceNode newNode mapping locations).roots.toList.Nodup)
    (selectedAfter childNode : TreeNode)
    (selectedAfterAt : (boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get selected = some selectedAfter)
    (selectedTag : selectedAfter.tag = selectedNode.tag)
    (childAt : (boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get child = some childNode)
    (childPath : GeneralBorrowExposedNonleafPrimaryPath.Path (boolAfter tree slot tag child source sourceNode newNode mapping locations) selected child)
    (initial : LocationTree) (initialRights : ZeroRights tree slot tag completion protections source initial)
    (normal : DuplicatePrefixBorrowAuthorization.Normal (boolAfter tree slot tag child source sourceNode newNode mapping locations) initial protections child)
    (reserved : (RawState initial child childNode).permission = .ReservedFrz false)
    (coherent : LocationCoherent (boolAfter tree slot tag child source sourceNode newNode mapping locations) initial protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile (boolAfter tree slot tag child source sourceNode newNode mapping locations) initial protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible (boolAfter tree slot tag child source sourceNode newNode mapping locations) initial)
    (short : (boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.size < 65536)
    (mode : ChildrenVisitMode) (range : ByteRange) :
    let after := boolAfter tree slot tag child source sourceNode newNode mapping locations
    let result := source_tree_access_at after initial (some child) .Write protections mode range
    source_access_status result = none ∧ LocationCoherent after (source_access_location result) protections ∧
      GeneralBorrowLocationSifaConsistency.Profile after (source_access_location result) protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible after (source_access_location result) ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal after (source_access_location result) protections child) ∧
      Authority after (S05ConcreteProtectedChildCompletion.extend completion child source) protections child (source_access_location result) ∧
      ∃ state,(source_access_location result).perms.get child = some state ∧ state.permission = .Unique := by
  let stage := boolStage tree slot tag child source sourceNode newNode mapping locations
  let after := boolAfter tree slot tag child source sourceNode newNode mapping locations
  have shape : treeShape after = treeShape stage := GeneralBorrowSifaView.preserves stage source .None
  have roots : after.roots = stage.roots := GeneralBorrowFreshMetadata.roots stage after shape
  have bound := (Array.getElem?_eq_some_iff.mp selectedSlot).1
  have selectedAfterSlot : after.roots[selectedPosition]? = some selected := by
    rw [roots]
    change (tree.roots.push slot.index)[selectedPosition]? = some selected
    simpa only [Array.getElem?_push,ite_eq_right (Nat.ne_of_lt bound)] using selectedSlot
  have initialAuthority := boolAfter_authority tree slot tag completion complete child source sourceNode newNode mapping locations vacant sourcePresent initial protections initialRights normal
  apply CurrentCallEmptyEntryWriteKind.write_unique after (S05ConcreteProtectedChildCompletion.extend completion child source) initial protections
    formed distinct selectedPosition selected child selectedAfter childNode selectedAfterSlot selectedAfterAt childAt childPath normal reserved initialAuthority
    (fun index node present path => boolChild_physical tree slot tag completion complete child source sourceNode newNode mapping locations
      vacant sourcePresent newParent selectedPosition selected selectedNode selectedSlot selectedPresent sourcePath index node present path)
    coherent profile possible
  intro position root rootAt different current currentAuthority cache sifa gp currentFrame
  have callback := zero_sifa_write_retained_callback tree slot tag completion protections complete depth order selectedPosition selected source selectedNode sourceNode
    selectedSlot selectedPresent sourcePresent sourcePath child newNode vacant hidden size mapping locations formed nextOrder initial current initialRights
    cache sifa gp currentAuthority short position root rootAt different currentFrame
  simpa only [selectedTag] using callback


private theorem zero_sifa_write_range_retained (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (protections : ProtectedTags) (complete : Completes tree completion)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (selectedPosition : Nat) (selected source : UniIndex) (selectedNode sourceNode : TreeNode)
    (selectedSlot : tree.roots[selectedPosition]? = some selected) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (sourcePresent : tree.nodes.get source = some sourceNode) (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree selected source)
    (child : UniIndex) (newNode : TreeNode) (vacant : (slot.after tag).nodes.get child = none) (hidden : newNode.isExposed = false)
    (newParent : newNode.parent = some source)
    (size : (slot.after tag).nodes.size ≤ (attachedNodes (slot.after tag).nodes child source sourceNode newNode).size)
    (mapping : UniKeyMap BorTag) (locations : DedupRangeMap LocationTree)
    (formed : GeneralBorrowStructuralHistoryState.GraphState (boolAfter tree slot tag child source sourceNode newNode mapping locations))
    (nextOrder : ParentTagOrder (boolAfter tree slot tag child source sourceNode newNode mapping locations))
    (distinct : (boolAfter tree slot tag child source sourceNode newNode mapping locations).roots.toList.Nodup)
    (selectedAfter childNode : TreeNode)
    (selectedAfterAt : (boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get selected = some selectedAfter)
    (selectedTag : selectedAfter.tag = selectedNode.tag)
    (childAt : (boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.get child = some childNode)
    (childPath : GeneralBorrowExposedNonleafPrimaryPath.Path (boolAfter tree slot tag child source sourceNode newNode mapping locations) selected child)
    (offset len : Size) (lower upper : UInt64)
    (mapped : (boolAfter tree slot tag child source sourceNode newNode mapping locations).indexOfTag childNode.tag = some child)
    (owned : OwnedOn (fun location => ZeroRights tree slot tag completion protections source location ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal (boolAfter tree slot tag child source sourceNode newNode mapping locations) location protections child)) lower upper (boolAfter tree slot tag child source sourceNode newNode mapping locations).locations)
    (well : (boolAfter tree slot tag child source sourceNode newNode mapping locations).locations.WellFormed)
    (runtime : GeneralRangeMapState.Every (fun location => LocationCoherent (boolAfter tree slot tag child source sourceNode newNode mapping locations) location protections ∧
      GeneralBorrowLocationSifaConsistency.Profile (boolAfter tree slot tag child source sourceNode newNode mapping locations) location protections ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible (boolAfter tree slot tag child source sourceNode newNode mapping locations) location) (boolAfter tree slot tag child source sourceNode newNode mapping locations).locations)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ (boolAfter tree slot tag child source sourceNode newNode mapping locations).locations.size.bytes.toNat)
    (requestLower : lower.toNat ≤ offset.bytes.toNat) (requestUpper : (offset.bytes+len.bytes).toNat ≤ upper.toNat)
    (short : (boolAfter tree slot tag child source sourceNode newNode mapping locations).nodes.size < 65536) (mode : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract (boolAfter tree slot tag child source sourceNode newNode mapping locations)
      (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal (boolAfter tree slot tag child source sourceNode newNode mapping locations) location protections child) ∧
        Authority (boolAfter tree slot tag child source sourceNode newNode mapping locations) (S05ConcreteProtectedChildCompletion.extend completion child source) protections child location)
      (fun location => LocationCoherent (boolAfter tree slot tag child source sourceNode newNode mapping locations) location protections ∧
        GeneralBorrowLocationSifaConsistency.Profile (boolAfter tree slot tag child source sourceNode newNode mapping locations) location protections ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible (boolAfter tree slot tag child source sourceNode newNode mapping locations) location)
      (fun _ _ => True) lower upper
      ((boolAfter tree slot tag child source sourceNode newNode mapping locations).performBorrowAccessRange (.concrete childNode.tag) offset len .Write protections mode) := by
  let after := boolAfter tree slot tag child source sourceNode newNode mapping locations
  apply GeneralBorrowConcreteRangeEntry.access after protections childNode.tag child mapped offset len .Write mode
    _ _ _ _ (fun location authority => ⟨authority.2,by
      obtain ⟨normal⟩ := authority.2
      exact boolAfter_authority tree slot tag completion complete child source sourceNode newNode mapping locations vacant sourcePresent location protections authority.1 normal⟩)
      (fun _ => trivial) _ lower upper owned well runtime bounds requestLower requestUpper
  intro location authority representation range
  obtain ⟨normal⟩ := authority.2
  have row := zero_sifa_child_write_retained tree slot tag completion protections complete depth order selectedPosition selected source selectedNode sourceNode
    selectedSlot selectedPresent sourcePresent sourcePath child newNode vacant hidden newParent size mapping locations formed nextOrder distinct selectedAfter childNode
    selectedAfterAt selectedTag childAt childPath location authority.1 normal representation.1 representation.2.1 representation.2.2 short mode range
  exact ⟨row.1,⟨row.2.2.2.2.1,row.2.2.2.2.2⟩,⟨row.2.1,row.2.2.1,row.2.2.2.1⟩,trivial⟩


private theorem extended_parent_live (tree : BorrowTree) (completion : Completion) (child source : UniIndex)
    (old : ∀ (query parent : UniIndex),completion.parents[query.toNat]?=some (some parent) → ∃ node,tree.nodeAt parent=some node)
    (sourceLive : ∃ node,tree.nodeAt source=some node) :
    ∀ (query parent : UniIndex),(S05ConcreteProtectedChildCompletion.extend completion child source).parents[query.toNat]?=some (some parent) →
      ∃ node,tree.nodeAt parent=some node := by
  intro query parent edge
  by_cases same : query=child
  · subst query
    rw [S05ConcreteProtectedChildCompletion.child_edge] at edge
    simp only [Option.some.injEq] at edge
    exact edge ▸ sourceLive
  · apply old query parent
    have extendedBound := (Array.getElem?_eq_some_iff.mp edge).1
    simp only [S05ConcreteProtectedChildCompletion.extend,Array.size_ofFn] at extendedBound
    by_cases bound : query.toNat<completion.parents.size
    · exact (S05ConcreteProtectedChildCompletion.old_parent completion child source query same bound).symm.trans edge
    · have missing : completion.parents[query.toNat]?=none := Array.getElem?_eq_none (by omega)
      have unequal : query.toNat≠child.toNat := fun eq => same (GeneralBorrowNodeUpdate.index_injective _ _ eq)
      simp [S05ConcreteProtectedChildCompletion.extend,extendedBound,unequal,missing] at edge

private theorem zero_fnentry_write_retained (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (complete : Completes tree completion) (oldFormed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (nextOrder : ParentTagOrder (slot.after tag)) (distinct : (slot.after tag).roots.toList.Nodup)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts (slot.after tag) global)
    (position : Nat) (root source : UniIndex) (rootNode sourceNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePresent : tree.nodes.get source = some sourceNode)
    (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root source)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : (slot.after tag).nodes.size+1 ≤ 4294967295)
    (clean : GeneralBorrowFreshFutureClean.Clean tree slot.index)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ (slot.after tag).locations.size.bytes.toNat)
    (owned : OwnedOn (ZeroRights tree slot tag completion global.protectedTags source) offset (offset+len) (slot.after tag).locations)
    (short : (slot.after tag).nodes.size+1 < 65536) :
    ∃ output : GeneralBorrowForestFnEntry.Output,
      GeneralBorrowForestFnEntry.operation (slot.after tag) global frame allocation sourceNode.tag offset len .VisitChildrenOfAccessed = .ok output ∧
      output.tag = global.nextPointerTag ∧ output.global = (GeneralBorrowFnEntryRegistration.registered global frame allocation room).1 ∧
      output.frame = (GeneralBorrowFnEntryRegistration.registered global frame allocation room).2 ∧
      output.access = (slot.after tag).performBorrowAccessRange (.concrete sourceNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
        .Read output.global.protectedTags .VisitChildrenOfAccessed ∧
      output.child = output.access.tree.newChild (Size.ofBytes offset) (.concrete sourceNode.tag) output.tag
        (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      let written := output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes offset) (Size.ofBytes len)
        .Write output.global.protectedTags .VisitChildrenOfAccessed
      written.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts written.tree output.global ∧
        written.tree.nodes = output.child.tree.nodes ∧ written.tree.locations.size = (slot.after tag).locations.size ∧
        written.tree.releaseProtector tag output.global.protectedTags = ⟨written.tree,.Released⟩ ∧
        ∃ child node,output.child.tree.indexOfTag output.tag = some child ∧ written.tree.nodes.get child = some node ∧
          node.tag = output.tag ∧ node.children = #[] ∧ node.isExposed = false ∧
          GeneralBorrowFreshActiveWithin.ActiveWithin written.tree child .Write offset (offset+len) ∧
          GeneralRangeMapState.Every (CurrentCallEmptyEntryWriteKind.WriteOnly child) written.tree.locations ∧
          OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal written.tree location output.global.protectedTags child) ∧
            Authority written.tree (S05ConcreteProtectedChildCompletion.extend completion child source) output.global.protectedTags child location)
            offset (offset+len) written.tree.locations ∧
          let released := written.tree.releaseProtector output.tag output.global.protectedTags
          released.status = .Released ∧ DuplicatePrefixBorrowContract.RuntimeFacts released.tree output.global ∧
          released.tree = {written.tree with locations := released.tree.locations} ∧
          released.tree.locations.size = (slot.after tag).locations.size ∧
          OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal released.tree location
              (output.global.endCall output.frame).protectedTags source) ∧
            Authority released.tree (S05ConcreteProtectedChildCompletion.extend completion child source)
              (output.global.endCall output.frame).protectedTags source location) offset (offset+len) released.tree.locations ∧
          (frame.protectedTags = #[(allocation,tag)] →
            DuplicatePrefixBorrowContract.RuntimeFacts released.tree (output.global.endCall output.frame)) ∧
          (frame.protectedTags = #[(allocation,tag)] →
            (released.tree.performBorrowAccessRange (.concrete sourceNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
              .Write (output.global.endCall output.frame).protectedTags .VisitChildrenOfAccessed).status = .Completed) ∧
          ParentTagOrder written.tree ∧ written.tree.nodes.size≤(slot.after tag).nodes.size+1 ∧
          CurrentCallEmptyEntrySourceData.Leaf written.tree tag ∧
          ∃ parentNode,written.tree.nodeAt source=some parentNode ∧ parentNode.tag=sourceNode.tag ∧ node.parent=some source ∧
            (∀ (query predecessor : UniIndex),(S05ConcreteProtectedChildCompletion.extend completion child source).parents[query.toNat]?=some (some predecessor) →
              ∃ predecessorNode,written.tree.nodeAt predecessor=some predecessorNode) ∧
            Nonempty (OrphanWriteFactory written.tree (S05ConcreteProtectedChildCompletion.extend completion child source) output.global.protectedTags child tag) := by
  obtain ⟨output,operation,tagEq,globalEq,frameEq,accessEq,readEq,readRuntime,readCapacity,childEq,readDone,childDone,
      childRuntime,childCapacity,growth,childOrder,oldOwned,normalChild,childLookup,normals,readInactive,childInactive⟩ :=
    zero_fnentry tree slot tag completion global frame allocation complete oldFormed depth order nextOrder distinct runtime position root source rootNode sourceNode
      rootSlot rootPresent sourcePresent sourcePath room nodeRoom clean offset len nonzero bounds owned (by omega)
  obtain ⟨_,_,_,_,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare (slot.after tag) global frame allocation room runtime
  have readNodes : output.access.tree.nodes = (slot.after tag).nodes := by rw [readEq]
  have readTags : output.access.tree.tagMapping = (slot.after tag).tagMapping := by rw [readEq]
  have readParent : output.access.tree.nodes.get source = some sourceNode := by
    rw [readNodes]
    exact S04ZeroRootObserverNormal.old_node tree slot tag source sourceNode sourcePresent
  have tagged : output.access.tree.indexOfTag sourceNode.tag = some source := readRuntime.formed.allocator.nodeTags source sourceNode readParent
  have freshRead : GeneralBorrowTagMap.Fresh output.access.tree.tagMapping output.tag := by rw [readTags,tagEq];exact fresh
  have readRoom : output.access.tree.nodes.size+1 ≤ 4294967295 := by rw [readNodes];exact nodeRoom
  have readBounds : offset.toNat+len.toNat ≤ output.access.tree.locations.size.bytes.toNat := by rw [readCapacity];exact bounds
  obtain ⟨child,mapping,locations,vacant,constructorEq,lookup⟩ := bool_constructor_representation tree slot tag output.access.tree output.global readEq readRuntime
    source sourceNode sourcePresent output.tag tagged freshRead readRoom offset len nonzero readBounds
  have afterEq : output.child.tree = boolAfter tree slot tag child source sourceNode (GeneralBorrowFreshChild.child output.tag source) mapping locations := by
    rw [childEq]
    exact constructorEq
  have lookupOutput : output.child.tree.indexOfTag output.tag = some child := by rw [childEq];exact lookup
  obtain ⟨activityChild,activityLookup,activity⟩ := GeneralBorrowConstructorChildActivity.Protected.construct output.access.tree output.global readRuntime
    sourceNode.tag output.tag source sourceNode tagged readParent freshRead readRoom offset len nonzero readBounds
  rw [←childEq] at activityLookup activity
  have activitySame : activityChild = child := Option.some.inj (activityLookup.symm.trans lookupOutput)
  subst activityChild
  obtain ⟨literalChild,literalLookup,literalReserved⟩ := mutable_constructor_shape output.access.tree output.global readRuntime
    sourceNode.tag output.tag source sourceNode tagged readParent freshRead readRoom offset len nonzero readBounds
  rw [←childEq] at literalLookup literalReserved
  have literalSame : literalChild = child := Option.some.inj (literalLookup.symm.trans lookupOutput)
  subst literalChild
  have childSame : normalChild = child := Option.some.inj (childLookup.symm.trans lookupOutput)
  subst normalChild
  rw [afterEq] at childRuntime childCapacity growth childOrder oldOwned normals activity childInactive literalReserved
  let after := boolAfter tree slot tag child source sourceNode (GeneralBorrowFreshChild.child output.tag source) mapping locations
  obtain ⟨selectedAfter,selectedAt,selectedTag,_,_,_⟩ := boolAfter_old_node tree slot tag child source sourceNode
    (GeneralBorrowFreshChild.child output.tag source) mapping locations vacant sourcePresent root rootNode rootPresent
  obtain ⟨childNode,childAt,childTag,parentEq,childLeaf,childHidden,childPermission⟩ := boolAfter_child_node tree slot tag child source sourceNode
    (GeneralBorrowFreshChild.child output.tag source) mapping locations vacant sourcePresent
  have oldPath : GeneralBorrowExposedNonleafPrimaryPath.Path after root source := by
    apply GeneralBorrowSharedAuthorizationGeometry.path_extension tree after _ root source sourcePath
    intro index node present
    obtain ⟨next,found,_,parent,_⟩ := boolAfter_old_node tree slot tag child source sourceNode
      (GeneralBorrowFreshChild.child output.tag source) mapping locations vacant sourcePresent index node present
    exact ⟨next,found,parent⟩
  have childPath : GeneralBorrowExposedNonleafPrimaryPath.Path after root child := .step oldPath childNode childAt parentEq
  let stage := boolStage tree slot tag child source sourceNode (GeneralBorrowFreshChild.child output.tag source) mapping locations
  have rootsEq : after.roots = (slot.after tag).roots := GeneralBorrowFreshMetadata.roots stage after (GeneralBorrowSifaView.preserves stage source .None)
  have distinctAfter : after.roots.toList.Nodup := by rw [rootsEq];exact distinct
  have shortAfter : after.nodes.size < 65536 := Nat.lt_of_le_of_lt growth short
  have afterBounds : offset.toNat+len.toNat ≤ after.locations.size.bytes.toNat := by rw [childCapacity];exact bounds
  have mapped : after.indexOfTag childNode.tag = some child := childRuntime.formed.allocator.nodeTags child childNode childAt
  have owners : OwnedOn (fun location => ZeroRights tree slot tag completion output.global.protectedTags source location ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal after location output.global.protectedTags child)) offset (offset+len) after.locations := by
    intro cursor valid positive start stop
    exact ⟨oldOwned cursor valid positive start stop,normals cursor valid positive start stop⟩
  have range := zero_sifa_write_range_retained tree slot tag completion output.global.protectedTags complete depth order position root source rootNode sourceNode
    rootSlot rootPresent sourcePresent sourcePath child (GeneralBorrowFreshChild.child output.tag source) vacant rfl rfl
    (bool_attached_size tree slot tag child source sourceNode (GeneralBorrowFreshChild.child output.tag source) vacant sourcePresent)
    mapping locations childRuntime.formed.toGraphState childOrder distinctAfter selectedAfter childNode selectedAt selectedTag childAt childPath
    (Size.ofBytes offset) (Size.ofBytes len) offset (offset+len) mapped owners childRuntime.formed.well
    (fun cursor valid => ⟨childRuntime.coherent cursor valid,childRuntime.formed.profile cursor valid,childRuntime.possible cursor valid⟩)
    afterBounds (Nat.le_refl _) (Nat.le_refl _) shortAfter .VisitChildrenOfAccessed
  change childNode.tag = output.tag at childTag
  rw [childTag] at range
  let written := after.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes offset) (Size.ofBytes len) .Write output.global.protectedTags .VisitChildrenOfAccessed
  have writtenEq : written.tree = {after with locations := written.tree.locations} := range.tree_eq
  have writtenRuntime : DuplicatePrefixBorrowContract.RuntimeFacts written.tree output.global := by
    rw [writtenEq]
    refine ⟨⟨⟨GeneralBorrowStructuralHistoryState.graph_locations after _ childRuntime.formed.toGraphState,range.well⟩,?_⟩,?_,?_,
      ⟨childRuntime.below.mapping,childRuntime.below.protectors⟩⟩
    · intro cursor valid
      exact ⟨(range.runtime cursor valid).2.1.present,(range.runtime cursor valid).2.1.vacant⟩
    · intro cursor valid
      exact (range.runtime cursor valid).1
    · intro cursor valid
      exact (range.runtime cursor valid).2.2
  obtain ⟨zeroNode,zeroAt,zeroTag,_,zeroLeaf,zeroHidden⟩ := boolAfter_zero_node tree slot tag child source sourceNode
    (GeneralBorrowFreshChild.child output.tag source) mapping locations vacant sourcePresent
  have zeroInactive : GeneralRangeMapState.Every (fun location => (GeneralBorrowWildcardVirtualLeaf.effective location slot.index zeroNode).accessed = false) after.locations := by
    intro cursor valid
    have old := childInactive cursor valid
    change (GeneralBorrowWildcardVirtualLeaf.effective after.locations.entries[cursor].data slot.index
      (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)).accessed = false at old
    cases stored : after.locations.entries[cursor].data.perms.get slot.index with
    | none => simp only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_none,TreeNode.defaultLocationState]
    | some state => simpa only [GeneralBorrowWildcardVirtualLeaf.effective,stored,Option.getD_some] using old
  have different : slot.index ≠ child := by
    intro same
    have original : (slot.after tag).nodes.get slot.index = some (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) := GeneralBorrowFreshLocation.get_same _ _ _
    rw [same,vacant] at original;cases original
  have sourceMapped : after.indexOfTag output.tag = some child := by simpa only [childTag] using mapped
  have normalRows : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal after location output.global.protectedTags child)) offset (offset+len) after.locations := by
    intro cursor valid positive start stop
    exact (owners cursor valid positive start stop).2
  have allReserved : GeneralRangeMapState.Every (fun row => (RawState row child childNode).permission = .ReservedFrz false) after.locations := by
    intro cursor valid
    have scalar := congrArg Prod.fst (zero_effective_shape after.locations.entries[cursor].data after.locations.entries[cursor].data
      (GeneralBorrowFreshChild.child output.tag source) childNode rfl childPermission child)
    exact scalar.trans (literalReserved cursor valid)
  let rowRuntime := fun location => LocationCoherent after location output.global.protectedTags ∧
    GeneralBorrowLocationSifaConsistency.Profile after location output.global.protectedTags ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible after location
  let prepared := after.locations.iterMut (Size.ofBytes offset) (Size.ofBytes len)
  have preparedRuntime := GeneralRangeMapSafety.iter_mut rowRuntime after.locations (Size.ofBytes offset) (Size.ofBytes len) childRuntime.formed.well
    (by intro cursor valid;exact ⟨childRuntime.coherent cursor valid,childRuntime.formed.profile cursor valid,childRuntime.possible cursor valid⟩) afterBounds
  have preparedReserved := GeneralRangeMapSafety.iter_mut (fun row => (RawState row child childNode).permission = .ReservedFrz false)
    after.locations (Size.ofBytes offset) (Size.ofBytes len) childRuntime.formed.well allReserved afterBounds
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on after.locations (Size.ofBytes offset) (Size.ofBytes len) childRuntime.formed.well afterBounds
    (fun location => ZeroRights tree slot tag completion output.global.protectedTags source location ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Normal after location output.global.protectedTags child)) offset (offset+len) owners
    (Nat.le_refl _) (Nat.le_refl _)
  have writeKinds := CurrentCallEmptyEntryWriteKind.range_write_kind after output.global.protectedTags output.tag child sourceMapped
    (Size.ofBytes offset) (Size.ofBytes len) .VisitChildrenOfAccessed childRuntime.formed.well afterBounds activity (by
      intro cursor valid
      let segment := prepared.segments[cursor]'valid
      have cursorBound : cursor < prepared.positions.size := by rw [preparedRuntime.lengths];exact valid
      obtain ⟨positionBound,selectionEq⟩ := preparedRuntime.selected cursor cursorBound
      have scalarRuntime : rowRuntime segment.data := by
        rw [show segment = prepared.state.entries[prepared.positions[cursor]] from selectionEq]
        exact preparedRuntime.every _ positionBound
      have reserved : (RawState segment.data child childNode).permission = .ReservedFrz false := by
        rw [show segment = prepared.state.entries[prepared.positions[cursor]] from selectionEq]
        exact preparedReserved.every _ positionBound
      obtain ⟨rawRights,⟨normal⟩⟩ := preparedOwners.2.2 cursor valid
      have row := zero_sifa_child_write_unique tree slot tag completion output.global.protectedTags complete depth order position root source rootNode sourceNode
        rootSlot rootPresent sourcePresent sourcePath child (GeneralBorrowFreshChild.child output.tag source) vacant rfl rfl
        (bool_attached_size tree slot tag child source sourceNode (GeneralBorrowFreshChild.child output.tag source) vacant sourcePresent)
        mapping locations childRuntime.formed.toGraphState childOrder distinctAfter selectedAfter childNode selectedAt selectedTag childAt childPath
        segment.data rawRights normal reserved scalarRuntime.1 scalarRuntime.2.1 scalarRuntime.2.2 shortAfter .VisitChildrenOfAccessed segment.range
      exact ⟨row.1,row.2.2.2.2.2.2⟩)
  have finalInactive := CurrentCallEmptyEntryQuietRelease.concrete after output.global childRuntime output.tag child slot.index offset len
    afterBounds normalRows childNode childAt sourceMapped zeroNode zeroAt zeroLeaf zeroHidden different zeroInactive .Write .VisitChildrenOfAccessed
  have finalZeroAt : written.tree.nodes.get slot.index = some zeroNode := by rw [range.nodes];exact zeroAt
  have finalZeroMapped : written.tree.indexOfTag tag = some slot.index := by
    have tagged := writtenRuntime.formed.allocator.nodeTags slot.index zeroNode finalZeroAt
    rw [zeroTag] at tagged
    exact tagged
  have zeroReleased := CurrentCallEmptyEntryQuietRelease.release written.tree tag slot.index zeroNode finalZeroMapped finalZeroAt zeroHidden
    finalInactive output.global.protectedTags
  have writtenOwned : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal written.tree location output.global.protectedTags child) ∧
      Authority written.tree (S05ConcreteProtectedChildCompletion.extend completion child source) output.global.protectedTags child location)
      offset (offset+len) written.tree.locations := by
    rw [writtenEq]
    intro cursor valid positive start stop
    obtain ⟨⟨normal⟩,authority⟩ := range.rows cursor valid positive start stop
    exact ⟨⟨⟨normal.component,normal.permissions⟩⟩,authority⟩
  have finalActive := GeneralBorrowFreshActiveWithinAccess.normal after output.tag (Size.ofBytes offset) (Size.ofBytes len) .Write
    output.global.protectedTags .VisitChildrenOfAccessed child offset (offset+len) childRuntime.formed.well afterBounds
    (Nat.le_refl _) (Nat.le_refl _) activity
  have finalBoolAt : written.tree.nodes.get child = some childNode := by rw [range.nodes];exact childAt
  have positive : offset.toNat < (offset+len).toNat := by
    have lenPos : 0 < len.toNat := by
      have nonzeroNat : len.toNat ≠ 0 := fun zero => nonzero (UInt64.toNat_inj.mp zero)
      omega
    have fits : offset.toNat+len.toNat < 2^64 := Nat.lt_of_le_of_lt afterBounds (UInt64.toNat_lt _)
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
    omega
  have boolReleased := CurrentCallEmptyEntryBoolRelease.release written.tree output.global
    (S05ConcreteProtectedChildCompletion.extend completion child source) writtenRuntime child childNode finalBoolAt childHidden offset len positive
    finalActive writtenOwned writeKinds.2 (by
      intro row ⟨normal⟩ authority cache sifa gp rangeNow
      rw [writtenEq] at normal authority cache sifa gp
      let baseNormal : DuplicatePrefixBorrowAuthorization.Normal after row output.global.protectedTags child := ⟨normal.component,normal.permissions⟩
      let baseProfile : GeneralBorrowLocationSifaConsistency.Profile after row output.global.protectedTags := ⟨sifa.present,sifa.vacant⟩
      have baseAuthority : Authority after (S05ConcreteProtectedChildCompletion.extend completion child source) output.global.protectedTags child row := authority
      have rawRights := boolAfter_rights_of_authority tree slot tag completion complete child source sourceNode
        (GeneralBorrowFreshChild.child output.tag source) mapping locations vacant sourcePresent row output.global.protectedTags baseAuthority
      have result := zero_sifa_child_write_retained tree slot tag completion output.global.protectedTags complete depth order position root source rootNode sourceNode
        rootSlot rootPresent sourcePresent sourcePath child (GeneralBorrowFreshChild.child output.tag source) vacant rfl rfl
        (bool_attached_size tree slot tag child source sourceNode (GeneralBorrowFreshChild.child output.tag source) vacant sourcePresent)
        mapping locations childRuntime.formed.toGraphState childOrder distinctAfter selectedAfter childNode selectedAt selectedTag childAt childPath
        row rawRights baseNormal cache baseProfile gp shortAfter .SkipChildrenOfAccessed rangeNow
      rw [writtenEq,source_access_locations]
      obtain ⟨done,outCache,outSifa,outGp,⟨outNormal⟩,outAuthority⟩ := result
      exact ⟨done,outCache,⟨outSifa.present,outSifa.vacant⟩,outGp,⟨⟨outNormal.component,outNormal.permissions⟩⟩,outAuthority⟩)
  rw [childTag] at boolReleased
  let released := written.tree.releaseProtector output.tag output.global.protectedTags
  have releasedBoolAt : released.tree.nodes.get child = some childNode := by rw [boolReleased.2.1];exact finalBoolAt
  have member : (allocation,childNode.tag) ∈ output.frame.protectedTags.toList := by
    rw [childTag,tagEq,frameEq]
    change (allocation,global.nextPointerTag) ∈ (frame.protectedTags.push (allocation,global.nextPointerTag)).toList
    simp
  have absent : (output.global.endCall output.frame).protectedTags.contains childNode.tag = false :=
    GeneralBorrowRelease.end_call_owned_absent output.global output.frame allocation childNode.tag member
  have releasedParents : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal released.tree location
      (output.global.endCall output.frame).protectedTags source) ∧ Authority released.tree
      (S05ConcreteProtectedChildCompletion.extend completion child source) (output.global.endCall output.frame).protectedTags source location)
      offset (offset+len) released.tree.locations := by
    intro cursor valid overlap start stop
    obtain ⟨⟨normal⟩,authority⟩ := boolReleased.2.2.2.2 cursor valid overlap start stop
    have raw := S05CompletedChildReanchor.end_call released.tree (S05ConcreteProtectedChildCompletion.extend completion child source)
      released.tree.locations.entries[cursor].data output.global output.frame allocation child source childNode
      (S05ConcreteProtectedChildCompletion.child_edge completion child source) releasedBoolAt member authority
    have restored := GeneralBorrowParentRestoreNormal.normal released.tree released.tree.locations.entries[cursor].data
      output.global.protectedTags (output.global.endCall output.frame).protectedTags child source childNode boolReleased.2.2.1.formed.toGraphState
      releasedBoolAt parentEq (GeneralBorrowRelease.end_call_weakens output.global output.frame) absent normal
    exact ⟨restored,raw⟩
  have releasedZeroAt : released.tree.nodes.get slot.index = some zeroNode := by rw [boolReleased.2.1];exact finalZeroAt
  have rootHidden : frame.protectedTags = #[(allocation,tag)] → S04ReturnReleaseParent.HiddenFrame released.tree output.frame := by
    intro frameTags
    have outputTags : output.frame.protectedTags = #[(allocation,tag),(allocation,output.tag)] := by
      rw [frameEq]
      change frame.protectedTags.push (allocation,global.nextPointerTag) = #[(allocation,tag),(allocation,output.tag)]
      rw [frameTags,tagEq]
      rfl
    intro row member index node present sameTag
    rw [outputTags] at member
    change row ∈ [(allocation,tag),(allocation,output.tag)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    have mappedNode := boolReleased.2.2.1.formed.allocator.nodeTags index node present
    rcases member with first | second
    · subst row
      have mappedZero := boolReleased.2.2.1.formed.allocator.nodeTags slot.index zeroNode releasedZeroAt
      rw [zeroTag] at mappedZero
      rw [sameTag] at mappedNode
      have same : index = slot.index := Option.some.inj (mappedNode.symm.trans mappedZero)
      subst index
      have sameNode : node = zeroNode := Option.some.inj (present.symm.trans releasedZeroAt)
      subst node
      exact zeroHidden
    · subst row
      have mappedBool := boolReleased.2.2.1.formed.allocator.nodeTags child childNode releasedBoolAt
      rw [childTag] at mappedBool
      rw [sameTag] at mappedNode
      have same : index = child := Option.some.inj (mappedNode.symm.trans mappedBool)
      subst index
      have sameNode : node = childNode := Option.some.inj (present.symm.trans releasedBoolAt)
      subst node
      exact childHidden
  have rootRuntime : frame.protectedTags = #[(allocation,tag)] →
      DuplicatePrefixBorrowContract.RuntimeFacts released.tree (output.global.endCall output.frame) :=
    fun frameTags => S05CompletedChildReanchor.runtime_end_call released.tree output.global output.frame boolReleased.2.2.1 (rootHidden frameTags)
  have returnWrite : frame.protectedTags = #[(allocation,tag)] →
      (released.tree.performBorrowAccessRange (.concrete sourceNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
        .Write (output.global.endCall output.frame).protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    intro frameTags
    let finalGlobal := output.global.endCall output.frame
    have finalRuntime := rootRuntime frameTags
    have currentEq : released.tree = {after with locations := released.tree.locations} := by
      rw [boolReleased.2.1,writtenEq]
    obtain ⟨parentAfter,parentAfterAt,parentTag,_,_,_⟩ := boolAfter_old_node tree slot tag child source sourceNode
      (GeneralBorrowFreshChild.child output.tag source) mapping locations vacant sourcePresent source sourceNode sourcePresent
    have parentAtReleased : released.tree.nodes.get source = some parentAfter := by rw [currentEq];exact parentAfterAt
    have returnMapped : released.tree.indexOfTag sourceNode.tag = some source := by
      have mapped := finalRuntime.formed.allocator.nodeTags source parentAfter parentAtReleased
      rw [parentTag] at mapped
      exact mapped
    have returnBounds : offset.toNat+len.toNat ≤ released.tree.locations.size.bytes.toNat := by
      rw [show released.tree.locations.size = written.tree.locations.size from boolReleased.2.2.2.1,range.capacity]
      exact afterBounds
    have rootBound := (Array.getElem?_eq_some_iff.mp rootSlot).1
    have rootAfterSlot : after.roots[position]? = some root := by
      rw [rootsEq]
      change (tree.roots.push slot.index)[position]? = some root
      simpa only [Array.getElem?_push,ite_eq_right (Nat.ne_of_lt rootBound)] using rootSlot
    let RP := fun location => LocationCoherent released.tree location finalGlobal.protectedTags ∧
      GeneralBorrowLocationSifaConsistency.Profile released.tree location finalGlobal.protectedTags ∧
      GeneralBorrowSnapshotReadRuntime.GlobalPossible released.tree location
    have contract : GeneralBorrowConcreteRangeInvariant.Contract released.tree (fun _ => True) RP (fun _ _ => True) offset (offset+len)
        (released.tree.performBorrowAccessRange (.concrete sourceNode.tag) (Size.ofBytes offset) (Size.ofBytes len) .Write finalGlobal.protectedTags .VisitChildrenOfAccessed) := by
      apply GeneralBorrowConcreteRangeEntry.access released.tree finalGlobal.protectedTags sourceNode.tag source returnMapped
        (Size.ofBytes offset) (Size.ofBytes len) .Write .VisitChildrenOfAccessed _ _ _ _
        (fun _ _ => trivial) (fun _ => trivial) _ offset (offset+len) releasedParents finalRuntime.formed.well
        (fun cursor valid => ⟨finalRuntime.coherent cursor valid,finalRuntime.formed.profile cursor valid,finalRuntime.possible cursor valid⟩)
        returnBounds (Nat.le_refl _) (Nat.le_refl _)
      intro row owner representation rangeNow
      obtain ⟨normal⟩ := owner.1
      rw [currentEq] at normal
      let baseNormal : DuplicatePrefixBorrowAuthorization.Normal after row finalGlobal.protectedTags source := ⟨normal.component,normal.permissions⟩
      have parentAuthority : Authority after (S05ConcreteProtectedChildCompletion.extend completion child source) finalGlobal.protectedTags source row := by
        intro index node present
        exact owner.2 index node (by rw [currentEq];exact present)
      have rawRights := boolAfter_rights_of_parent_authority tree slot tag completion complete child source sourceNode
        (GeneralBorrowFreshChild.child output.tag source) mapping locations vacant sourcePresent row finalGlobal.protectedTags parentAuthority
      dsimp only [RP] at representation ⊢
      rw [currentEq] at representation
      let baseProfile : GeneralBorrowLocationSifaConsistency.Profile after row finalGlobal.protectedTags :=
        ⟨representation.2.1.present,representation.2.1.vacant⟩
      have accessed := CurrentCallEmptyEntryRootLoop.write after row finalGlobal.protectedTags childRuntime.formed.toGraphState distinctAfter
        position root source selectedAfter parentAfter rootAfterSlot selectedAt parentAfterAt oldPath baseNormal
        representation.1 baseProfile representation.2.2 (by
          intro observerPosition observer observerAt different current cache profile gp currentFrame
          have callback := zero_sifa_write_callback tree slot tag completion finalGlobal.protectedTags complete depth order position root source rootNode sourceNode
            rootSlot rootPresent sourcePresent sourcePath child (GeneralBorrowFreshChild.child output.tag source) vacant rfl
            (bool_attached_size tree slot tag child source sourceNode (GeneralBorrowFreshChild.child output.tag source) vacant sourcePresent)
            mapping locations childRuntime.formed.toGraphState childOrder row current rawRights cache profile gp shortAfter
            observerPosition observer observerAt different currentFrame
          simpa only [selectedTag] using callback) .VisitChildrenOfAccessed rangeNow
      rw [currentEq,source_access_locations]
      exact ⟨accessed.1,trivial,⟨accessed.2.1,⟨accessed.2.2.1.present,accessed.2.2.1.vacant⟩,accessed.2.2.2⟩,trivial⟩
    exact contract.completed
  have finalOrder : ParentTagOrder written.tree := GeneralBorrowParentTagInvariant.nodes_frame after written.tree range.nodes childOrder
  have finalGrowth : written.tree.nodes.size≤(slot.after tag).nodes.size+1 := by rw [range.nodes];exact growth
  have finalLeaf : CurrentCallEmptyEntrySourceData.Leaf written.tree tag :=
    ⟨slot.index,zeroNode,finalZeroMapped,finalZeroAt,zeroTag,zeroLeaf,zeroHidden,finalInactive⟩
  obtain ⟨parentWritten,parentWrittenAt,parentWrittenTag,_,_,_⟩ := boolAfter_old_node tree slot tag child source sourceNode
    (GeneralBorrowFreshChild.child output.tag source) mapping locations vacant sourcePresent source sourceNode sourcePresent
  have parentAtWritten : written.tree.nodeAt source=some parentWritten := by
    change written.tree.nodes.get source=_
    rw [range.nodes];exact parentWrittenAt
  have oldParentsLive : ∀ (query predecessor : UniIndex),completion.parents[query.toNat]?=some (some predecessor) →
      ∃ predecessorNode,written.tree.nodeAt predecessor=some predecessorNode := by
    intro query predecessor edge
    obtain ⟨oldNode,oldAt⟩ := (complete.2.2.2.2.2.2 query predecessor edge).2.1
    obtain ⟨next,nextAt,_,_,_,_⟩ := boolAfter_old_node tree slot tag child source sourceNode
      (GeneralBorrowFreshChild.child output.tag source) mapping locations vacant sourcePresent predecessor oldNode oldAt
    refine ⟨next,?_⟩
    change written.tree.nodes.get predecessor=_
    rw [range.nodes];exact nextAt
  have parentLive := extended_parent_live written.tree completion child source oldParentsLive ⟨parentWritten,parentAtWritten⟩
  have factory : Nonempty (OrphanWriteFactory written.tree (S05ConcreteProtectedChildCompletion.extend completion child source) output.global.protectedTags child tag) := by
    refine ⟨⟨position,root,selectedAfter,?_,?_,?_,slot.index,tree.roots.size,finalZeroMapped,?_,?_,?_,?_,?_,?_,?_⟩⟩
    · have bound := (Array.getElem?_eq_some_iff.mp rootSlot).1
      rw [writtenEq,rootsEq]
      change (tree.roots.push slot.index)[position]?=some root
      simpa only [Array.getElem?_push,ite_eq_right (Nat.ne_of_lt bound)] using rootSlot
    · change written.tree.nodes.get root=some selectedAfter
      rw [range.nodes];exact selectedAt
    · apply GeneralBorrowSharedAuthorizationGeometry.path_extension after written.tree _ root child childPath
      intro query node atNode
      refine ⟨node,?_,rfl⟩
      change written.tree.nodes.get query=some node
      rw [range.nodes];exact atNode
    · rw [writtenEq,rootsEq]
      change (tree.roots.push slot.index)[tree.roots.size]?=some slot.index
      simp
    · have bound := (Array.getElem?_eq_some_iff.mp rootSlot).1
      omega
    · exact (boolChild_ancestry tree slot tag completion complete child source vacant sourceNode sourcePresent).2
    · intro equal
      rw [equal,slot.vacant] at rootPresent
      cases rootPresent
    · rw [writtenEq]
      exact distinctAfter
    · intro query node present path
      have back : ∀ first last,GeneralBorrowExposedNonleafPrimaryPath.Path written.tree first last →
          GeneralBorrowExposedNonleafPrimaryPath.Path after first last := by
        intro first last actual
        apply GeneralBorrowSharedAuthorizationGeometry.path_extension written.tree after _ first last actual
        intro index old oldAt
        refine ⟨old,?_,rfl⟩
        rw [←range.nodes];exact oldAt
      have forward : ∀ first last,GeneralBorrowExposedNonleafPrimaryPath.Path after first last →
          GeneralBorrowExposedNonleafPrimaryPath.Path written.tree first last := by
        intro first last actual
        apply GeneralBorrowSharedAuthorizationGeometry.path_extension after written.tree _ first last actual
        intro index old oldAt
        refine ⟨old,?_,rfl⟩
        rw [range.nodes];exact oldAt
      have oldAt : after.nodes.get query=some node := by rw [←range.nodes];exact present
      have classification := boolChild_physical tree slot tag completion complete child source sourceNode
        (GeneralBorrowFreshChild.child output.tag source) mapping locations vacant sourcePresent rfl
        position root rootNode rootSlot rootPresent sourcePath query node oldAt (back root query path)
      exact ⟨fun below => forward query child (classification.mp below),fun physical => classification.mpr (back query child physical)⟩
    · intro current currentAuthority currentPosition currentRoot currentAt differentRoot consistent
      rw [writtenEq] at currentAuthority currentAt
      have authorityBefore : Authority after (S05ConcreteProtectedChildCompletion.extend completion child source) output.global.protectedTags child current := currentAuthority
      have rootBefore : after.roots[currentPosition]?=some currentRoot := currentAt
      have consistencyBefore : ∀ index node,after.nodes.get index=some node → GeneralBorrowExposedNonleafPrimaryPath.Path after currentRoot index →
          GeneralBorrowSifaPermissionConsistency.Consistent ((current.perms.get index).getD node.defaultLocationState) (output.global.protectedTags.contains node.tag) := by
        intro index node present path
        apply consistent index node
        · change written.tree.nodes.get index=some node
          rw [range.nodes];exact present
        · apply GeneralBorrowSharedAuthorizationGeometry.path_extension after written.tree _ currentRoot index path
          intro query queryNode queryAt
          refine ⟨queryNode,?_,rfl⟩
          change written.tree.nodes.get query=some queryNode
          rw [range.nodes];exact queryAt
      have rights := boolAfter_rights_of_authority tree slot tag completion complete child source sourceNode
        (GeneralBorrowFreshChild.child output.tag source) mapping locations vacant sourcePresent current output.global.protectedTags authorityBefore
      obtain ⟨queries⟩ := zero_sifa_write_queries tree slot tag completion output.global.protectedTags complete depth order position root source rootNode sourceNode
        rootSlot rootPresent sourcePresent sourcePath child (GeneralBorrowFreshChild.child output.tag source) vacant rfl
        (bool_attached_size tree slot tag child source sourceNode (GeneralBorrowFreshChild.child output.tag source) vacant sourcePresent)
        mapping locations childRuntime.formed.toGraphState current current rights authorityBefore currentPosition currentRoot rootBefore differentRoot
        (by intro;intro;intro;intro;rfl) consistencyBefore
      obtain ⟨afterDepth⟩ := childRuntime.formed.depth
      rw [writtenEq,selectedTag]
      exact ⟨write_queries_locations after (S05ConcreteProtectedChildCompletion.extend completion child source) output.global.protectedTags
        child currentRoot currentPosition (some rootNode.tag) current afterDepth written.tree.locations queries⟩
  refine ⟨output,operation,tagEq,globalEq,frameEq,accessEq,childEq,readDone,childDone,?_,?_,?_,?_,?_,?_⟩
  · rw [afterEq]
    exact range.completed
  · rw [afterEq]
    exact writtenRuntime
  · rw [afterEq]
    exact range.nodes
  · rw [afterEq]
    exact range.capacity.trans childCapacity


  · rw [afterEq]
    exact zeroReleased
  · refine ⟨child,childNode,lookupOutput,?_,childTag,childLeaf,childHidden,?_,?_,?_,?_⟩
    · rw [afterEq];exact finalBoolAt
    · rw [afterEq];exact finalActive
    · rw [afterEq];exact writeKinds.2
    · rw [afterEq];exact writtenOwned
    · rw [afterEq]
      exact ⟨boolReleased.1,boolReleased.2.2.1,boolReleased.2.1,boolReleased.2.2.2.1.trans (range.capacity.trans childCapacity),releasedParents,rootRuntime,returnWrite,finalOrder,finalGrowth,finalLeaf,parentWritten,parentAtWritten,parentWrittenTag,parentEq,parentLive,factory⟩

private theorem zero_fnentry_write (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (complete : Completes tree completion) (oldFormed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (nextOrder : ParentTagOrder (slot.after tag)) (distinct : (slot.after tag).roots.toList.Nodup)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts (slot.after tag) global)
    (position : Nat) (root source : UniIndex) (rootNode sourceNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePresent : tree.nodes.get source = some sourceNode)
    (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root source)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : (slot.after tag).nodes.size+1 ≤ 4294967295)
    (clean : GeneralBorrowFreshFutureClean.Clean tree slot.index)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ (slot.after tag).locations.size.bytes.toNat)
    (owned : OwnedOn (ZeroRights tree slot tag completion global.protectedTags source) offset (offset+len) (slot.after tag).locations)
    (short : (slot.after tag).nodes.size+1 < 65536) :
    ∃ output : GeneralBorrowForestFnEntry.Output,
      GeneralBorrowForestFnEntry.operation (slot.after tag) global frame allocation sourceNode.tag offset len .VisitChildrenOfAccessed = .ok output ∧
      output.tag = global.nextPointerTag ∧ output.global = (GeneralBorrowFnEntryRegistration.registered global frame allocation room).1 ∧
      output.frame = (GeneralBorrowFnEntryRegistration.registered global frame allocation room).2 ∧
      output.access = (slot.after tag).performBorrowAccessRange (.concrete sourceNode.tag) (Size.ofBytes offset) (Size.ofBytes len)
        .Read output.global.protectedTags .VisitChildrenOfAccessed ∧
      output.child = output.access.tree.newChild (Size.ofBytes offset) (.concrete sourceNode.tag) output.tag
        (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      let written := output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes offset) (Size.ofBytes len)
        .Write output.global.protectedTags .VisitChildrenOfAccessed
      written.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts written.tree output.global ∧
        written.tree.nodes = output.child.tree.nodes ∧ written.tree.locations.size = (slot.after tag).locations.size := by
  obtain ⟨output,operation,tagEq,globalEq,frameEq,accessEq,childEq,readDone,childDone,writeDone,writtenRuntime,nodes,capacity,_,_⟩ :=
    zero_fnentry_write_retained tree slot tag completion global frame allocation complete oldFormed depth order nextOrder distinct runtime
      position root source rootNode sourceNode rootSlot rootPresent sourcePresent sourcePath room nodeRoom clean offset len nonzero bounds owned short
  exact ⟨output,operation,tagEq,globalEq,frameEq,accessEq,childEq,readDone,childDone,writeDone,writtenRuntime,nodes,capacity⟩


/-- Derived pre-release Bool rights on one actual tree and one fixed ancestry.
This is output data for the real empty helper/release consumer. -/
structure BoolHoldings (tree : BorrowTree) (global : GlobalState) (tag qTag : BorTag) (provenance : Provenance) (offset : UInt64) where
  completion : Completion
  child : UniIndex
  node : TreeNode
  mapped : tree.indexOfTag tag=some child
  present : tree.nodeAt child=some node
  nodeTag : node.tag=tag
  leaf : node.children=#[]
  hidden : node.isExposed=false
  active : GeneralBorrowFreshActiveWithin.ActiveWithin tree child .Write offset (offset+1)
  owned : OwnedOn (fun row => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree row global.protectedTags child) ∧
    Authority tree completion global.protectedTags child row) offset (offset+1) tree.locations
  writeOnly : GeneralRangeMapState.Every (CurrentCallEmptyEntryWriteKind.WriteOnly child) tree.locations
  parent : UniIndex
  parentNode : TreeNode
  parentAt : tree.nodeAt parent=some parentNode
  edge : completion.parents[child.toNat]?=some (some parent)
  parentProvenance : match provenance with | .concrete _ oldTag => oldTag=parentNode.tag | .wildcard => parentNode.isExposed=true
  parentLive : ∀ (query parent : UniIndex),completion.parents[query.toNat]?=some (some parent) → ∃ parentNode,tree.nodeAt parent=some parentNode
  physicalOrComplete : node.parent=some parent ∨ Completes tree completion
  geometry : Completes tree completion ∨ Nonempty (OrphanWriteFactory tree completion global.protectedTags child qTag)
  wildcardComplete : provenance=.wildcard → Completes tree completion

private theorem complete_bool_holdings (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (node : TreeNode) (present : tree.nodes.get pointer.grant=some node)
    (provenance : match pointer.value.provenance with | .concrete _ tag => tag=node.tag | .wildcard => node.isExposed=true)
    (room : global.nextPointerTag.value<18446744073709551615)
    (nodeRoom : tree.nodes.size+1≤4294967295) (short : tree.nodes.size+1<65536)
    (offset : UInt64) (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+1) tree.locations)
    (qTag : BorTag) (borrow : CurrentCallEmptyEntryCompleteRelease.Result tree global frame allocation completion pointer offset room) :
    Nonempty (BoolHoldings (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree borrow.output.global borrow.output.tag qTag pointer.value.provenance offset) := by
  have reserved := complete_constructor_reserved tree global frame allocation completion runtime complete order pointer node present provenance room nodeRoom short offset bounds owned borrow
  obtain ⟨normal,authority,kind⟩ := CurrentCallEmptyEntryCompleteHoldings.of_reserved tree global frame allocation completion runtime complete order
    pointer node present provenance room nodeRoom short offset bounds owned borrow reserved
  have childAt : (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.nodeAt borrow.child=some borrow.node := by
    change (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.nodes.get borrow.child=_
    rw [borrow.writeNodes];exact borrow.childAt
  have mapped := borrow.writeRuntime.formed.allocator.nodeTags borrow.child borrow.node childAt
  rw [borrow.nodeTag] at mapped
  have nodes : (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree.nodes=
      (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.nodes := by
      have known := congrArg BorrowTree.nodes borrow.releaseShape
      exact known
  have parentAt : (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.nodeAt pointer.grant=some borrow.originalNode := by
    change (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.nodes.get pointer.grant=_
    rw [←nodes];exact borrow.originalPresent
  refine ⟨⟨S05ConcreteProtectedChildCompletion.extend completion borrow.child pointer.grant,borrow.child,borrow.node,mapped,childAt,borrow.nodeTag,borrow.leaf,borrow.hidden,
    borrow.writeActive,?_,kind,pointer.grant,borrow.originalNode,parentAt,S05ConcreteProtectedChildCompletion.child_edge completion borrow.child pointer.grant,
    borrow.originalProvenance,?_,.inr borrow.writeComplete,.inl borrow.writeComplete,(fun _=>borrow.writeComplete)⟩⟩
  · intro cursor valid positive start stop
    exact ⟨normal cursor valid positive start stop,authority cursor valid positive start stop⟩
  · intro query parent edge
    exact (borrow.writeComplete.2.2.2.2.2.2 query parent edge).2.1

/-- Derived operational data for the immediate empty root Return consumer.
The q-allocation alternative is an actual finite Effect output, never a loan. -/
structure RootOperation (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (provenance : Provenance) (offset : UInt64) (qAllocation : Option AllocId) (qTag : BorTag)
    (room : global.nextPointerTag.value < 18446744073709551615) where
  output : GeneralBorrowForestFnEntry.Output
  actual : CandidateCurrentFnEntryRaw.operation tree global frame allocation provenance offset 1 = .ok output
  tag : output.tag = global.nextPointerTag
  globalEq : output.global = (GeneralBorrowFnEntryRegistration.registered global frame allocation room).1
  frameEq : output.frame = frame.addProtector allocation global.nextPointerTag
  readCompleted : output.access.status = .Completed
  childCompleted : output.child.outcome = .ok ()
  writeCompleted : (CurrentCallEmptyEntryCompleteRelease.written output offset).status = .Completed
  writeRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallEmptyEntryCompleteRelease.written output offset).tree output.global
  writeCapacity : (CurrentCallEmptyEntryCompleteRelease.written output offset).tree.locations.size = tree.locations.size
  qRelease : qAllocation = some allocation →
    (CurrentCallEmptyEntryCompleteRelease.written output offset).tree.releaseProtector qTag output.global.protectedTags =
      ⟨(CurrentCallEmptyEntryCompleteRelease.written output offset).tree,.Released⟩
  releaseCompleted : (CurrentCallEmptyEntryCompleteRelease.released output offset).status = .Released
  releaseRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallEmptyEntryCompleteRelease.released output offset).tree output.global
  releaseShape : (CurrentCallEmptyEntryCompleteRelease.released output offset).tree =
    {(CurrentCallEmptyEntryCompleteRelease.written output offset).tree with locations := (CurrentCallEmptyEntryCompleteRelease.released output offset).tree.locations}
  releaseCapacity : (CurrentCallEmptyEntryCompleteRelease.released output offset).tree.locations.size = tree.locations.size
  afterRuntime : DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallEmptyEntryCompleteRelease.released output offset).tree (output.global.endCall output.frame)
  originalWrite : ((CurrentCallEmptyEntryCompleteRelease.released output offset).tree.performBorrowAccessRange
      (S04ReturnBorrowBridge.extra provenance) (Size.ofBytes offset) (Size.ofBytes 1) .Write
      (output.global.endCall output.frame).protectedTags .VisitChildrenOfAccessed).status = .Completed
  order : ParentTagOrder (CurrentCallEmptyEntryCompleteRelease.written output offset).tree
  writeNodes : (CurrentCallEmptyEntryCompleteRelease.written output offset).tree.nodes=output.child.tree.nodes
  growth : (CurrentCallEmptyEntryCompleteRelease.written output offset).tree.nodes.size≤tree.nodes.size+1
  qLeaf : qAllocation=some allocation → CurrentCallEmptyEntrySourceData.Leaf (CurrentCallEmptyEntryCompleteRelease.written output offset).tree qTag
  holdings : Nonempty (BoolHoldings (CurrentCallEmptyEntryCompleteRelease.written output offset).tree output.global output.tag qTag provenance offset)
  hidden : S04ReturnReleaseParent.HiddenFrame (CurrentCallEmptyEntryCompleteRelease.written output offset).tree output.frame
  bounds : offset.toNat+1≤(CurrentCallEmptyEntryCompleteRelease.written output offset).tree.locations.size.bytes.toNat

private theorem rootOperation_of_complete (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (pointer : PointerInstance) (offset : UInt64)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (borrow : CurrentCallEmptyEntryCompleteRelease.Result tree global frame allocation completion pointer offset room)
    (bounds : offset.toNat+1 ≤ tree.locations.size.bytes.toNat) (short : tree.nodes.size+1 < 65536)
    (qAllocation : Option AllocId) (qTag : BorTag)
    (qRelease : qAllocation = some allocation →
      (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.releaseProtector qTag borrow.output.global.protectedTags =
        ⟨(CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree,.Released⟩)
    (qLeaf : qAllocation=some allocation → CurrentCallEmptyEntrySourceData.Leaf
      (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree qTag)
    (hidden : S04ReturnReleaseParent.HiddenFrame (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree borrow.output.frame)
    (holdings : Nonempty (BoolHoldings (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree borrow.output.global borrow.output.tag qTag pointer.value.provenance offset)) :
    Nonempty (RootOperation tree global frame allocation pointer.value.provenance offset qAllocation qTag room) := by
  have releasedShort : (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree.nodes.size < 65536 := by
    rw [borrow.releaseShape]
    change (CurrentCallEmptyEntryCompleteRelease.written borrow.output offset).tree.nodes.size < 65536
    rw [borrow.writeNodes]
    exact Nat.lt_of_le_of_lt borrow.metadata.growth short
  have releasedBounds : offset.toNat+1 ≤ (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree.locations.size.bytes.toNat := by
    rw [borrow.releaseCapacity]
    exact bounds
  refine ⟨⟨borrow.output,borrow.actual,borrow.tag,borrow.globalEq,borrow.frameEq,borrow.readCompleted,borrow.childCompleted,borrow.writeCompleted,
    borrow.writeRuntime,borrow.writeCapacity,qRelease,borrow.releaseCompleted,borrow.releaseRuntime,borrow.releaseShape,borrow.releaseCapacity,
    borrow.afterRuntime hidden,?_,borrow.writeOrder,borrow.writeNodes,by rw [borrow.writeNodes];exact borrow.metadata.growth,qLeaf,holdings,?_,?_⟩⟩
  · exact CurrentCallRootRelease.write_original (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree
      (borrow.output.global.endCall borrow.output.frame) (S05ConcreteProtectedChildCompletion.extend completion borrow.child pointer.grant)
      (borrow.afterRuntime hidden) borrow.releaseComplete borrow.releaseOrder pointer.grant borrow.originalNode borrow.originalPresent
      pointer.value.provenance borrow.originalProvenance offset releasedBounds borrow.originalOwned releasedShort
  · intro row member index node present sameTag
    apply hidden row member index node _ sameTag
    change (CurrentCallEmptyEntryCompleteRelease.released borrow.output offset).tree.nodes.get index=some node
    rw [borrow.releaseShape]
    exact present
  · rw [borrow.writeCapacity]
    exact bounds


private theorem rootOperation_complete (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (node : TreeNode) (present : tree.nodes.get pointer.grant=some node)
    (provenance : match pointer.value.provenance with | .concrete _ tag => tag=node.tag | .wildcard => node.isExposed=true)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1≤4294967295) (short : tree.nodes.size+1<65536)
    (offset : UInt64) (bounds : offset.toNat+1≤tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+1) tree.locations)
    (qAllocation : Option AllocId) (qTag : BorTag)
    (shape : frame.protectedTags = match qAllocation with | none => #[] | some id => #[(id,qTag)])
    (quiet : qAllocation=some allocation → CurrentCallEmptyEntrySourceData.Leaf tree qTag)
    (absent : qAllocation≠some allocation → tree.indexOfTag qTag=none)
    (parentDifferent : node.tag≠qTag) (nextDifferent : global.nextPointerTag≠qTag) :
    Nonempty (RootOperation tree global frame allocation pointer.value.provenance offset qAllocation qTag room) := by
  obtain ⟨borrow⟩ := CurrentCallEmptyEntryCompleteRelease.construct tree global frame allocation completion runtime complete order
    pointer node present provenance room nodeRoom short offset bounds owned
  have holdings := complete_bool_holdings tree global frame allocation completion runtime complete order pointer node present provenance room nodeRoom short offset bounds owned qTag borrow
  cases qCase : qAllocation with
  | none =>
    apply rootOperation_of_complete tree global frame allocation completion pointer offset room borrow bounds short none qTag
    · intro impossible;cases impossible
    · intro impossible;cases impossible
    · exact CurrentCallEmptyEntryHiddenFrame.empty borrow (by simpa only [qCase] using shape)
    · exact holdings
  | some id =>
    have frameShape : frame.protectedTags=#[(id,qTag)] := by simpa only [qCase] using shape
    by_cases same : id=allocation
    · subst id
      obtain ⟨query,qNode,_,qPresent,qNodeTag,qLeaf,qHidden,qInactive⟩ := quiet qCase
      have different : query≠pointer.grant := by
        intro eq
        subst query
        have equal : qNode=node := Option.some.inj (qPresent.symm.trans present)
        subst qNode
        exact parentDifferent qNodeTag
      obtain ⟨next,nextPresent,nextTag,nextLeaf,nextHidden,nextInactive,qReleased⟩ := CurrentCallEmptyEntryQuietCompleteBorrow.retained tree global frame allocation completion
        runtime complete order pointer node present provenance room nodeRoom short offset bounds owned borrow
        query qNode qPresent qLeaf qHidden different qInactive
      apply rootOperation_of_complete tree global frame allocation completion pointer offset room borrow bounds short (some allocation) qTag
      · intro _;simpa only [qNodeTag] using qReleased
      · intro _
        have mapped := borrow.writeRuntime.formed.allocator.nodeTags query next nextPresent
        rw [nextTag,qNodeTag] at mapped
        exact ⟨query,next,mapped,nextPresent,nextTag.trans qNodeTag,nextLeaf,nextHidden,nextInactive⟩
      · exact CurrentCallEmptyEntryHiddenFrame.singleton_present borrow allocation qTag query next frameShape nextPresent (nextTag.trans qNodeTag) nextHidden
      · exact holdings
    · apply rootOperation_of_complete tree global frame allocation completion pointer offset room borrow bounds short (some id) qTag
      · intro impossible;exact False.elim (same (Option.some.inj impossible))
      · intro impossible;exact False.elim (same (Option.some.inj impossible))
      · exact CurrentCallEmptyEntryHiddenFrame.singleton_other tree global frame allocation completion runtime complete order pointer node present provenance
          room nodeRoom short offset bounds owned borrow id qTag frameShape
          (absent (by rw [qCase];exact fun eq => same (Option.some.inj eq)))
          (borrow.tag ▸ nextDifferent)
      · exact holdings

private theorem rootOperation_of_zero (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (global : GlobalState) (frame : FrameState) (allocation supplied : AllocId)
    (complete : Completes tree completion) (oldFormed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (order : ParentTagOrder tree)
    (nextOrder : ParentTagOrder (slot.after tag)) (distinct : (slot.after tag).roots.toList.Nodup)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts (slot.after tag) global)
    (position : Nat) (root source : UniIndex) (rootNode sourceNode : TreeNode)
    (rootSlot : tree.roots[position]? = some root) (rootPresent : tree.nodes.get root = some rootNode)
    (sourcePresent : tree.nodes.get source = some sourceNode)
    (sourcePath : GeneralBorrowExposedNonleafPrimaryPath.Path tree root source)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : (slot.after tag).nodes.size+1 ≤ 4294967295)
    (clean : GeneralBorrowFreshFutureClean.Clean tree slot.index)
    (offset : UInt64) (bounds : offset.toNat+1 ≤ (slot.after tag).locations.size.bytes.toNat)
    (owned : OwnedOn (ZeroRights tree slot tag completion global.protectedTags source) offset (offset+1) (slot.after tag).locations)
    (short : (slot.after tag).nodes.size+1 < 65536)
    (frameTags : frame.protectedTags = #[(allocation,tag)]) :
    Nonempty (RootOperation (slot.after tag) global frame allocation (.concrete supplied sourceNode.tag) offset (some allocation) tag room) := by
  obtain ⟨output,operation,tagEq,globalEq,frameEq,_,_,readDone,childDone,writeDone,writtenRuntime,writeNodes,capacity,qReleased,certificate⟩ :=
    zero_fnentry_write_retained tree slot tag completion global frame allocation complete oldFormed depth order nextOrder distinct runtime
      position root source rootNode sourceNode rootSlot rootPresent sourcePresent sourcePath room nodeRoom clean offset 1 (by decide) bounds owned short
  obtain ⟨child,node,lookup,childAt,nodeTag,nodeLeaf,nodeHidden,active,writeOnly,ownedChild,releasedDone,releasedRuntime,releasedShape,releasedCapacity,_,rootRuntime,returnWrite,writeOrder,writeGrowth,qLeaf,parentNode,parentAt,parentTag,parentEq,parentLive,factory⟩ := certificate
  have mapped := writtenRuntime.formed.allocator.nodeTags child node childAt
  rw [nodeTag] at mapped
  have holdings : Nonempty (BoolHoldings (CurrentCallEmptyEntryCompleteRelease.written output offset).tree output.global output.tag tag (.concrete supplied sourceNode.tag) offset) :=
    ⟨⟨S05ConcreteProtectedChildCompletion.extend completion child source,child,node,mapped,childAt,nodeTag,nodeLeaf,nodeHidden,
      active,ownedChild,writeOnly,source,parentNode,parentAt,S05ConcreteProtectedChildCompletion.child_edge completion child source,parentTag.symm,parentLive,.inl parentEq,.inr factory,(by intro impossible;cases impossible)⟩⟩
  refine ⟨⟨output,?_,tagEq,globalEq,frameEq,readDone,childDone,writeDone,writtenRuntime,capacity,
    (fun _ => qReleased),releasedDone,releasedRuntime,releasedShape,releasedCapacity,rootRuntime frameTags,returnWrite frameTags,writeOrder,writeNodes,writeGrowth,(fun _=>qLeaf),holdings,?_,?_⟩⟩
  · simpa only [CandidateCurrentFnEntryRaw.operation] using operation
  · intro row member index current present sameTag
    rw [frameEq] at member
    change row ∈ (frame.addProtector allocation global.nextPointerTag).protectedTags.toList at member
    rw [show (frame.addProtector allocation global.nextPointerTag).protectedTags=
      frame.protectedTags.push (allocation,global.nextPointerTag) from rfl,frameTags] at member
    simp at member
    obtain ⟨qIndex,qNode,qMapped,qAt,qNodeTag,_,qHidden,_⟩ := qLeaf
    have actualMapped := writtenRuntime.formed.allocator.nodeTags index current present
    rcases member with q | b
    · subst row
      rw [sameTag] at actualMapped
      have equal : index=qIndex := Option.some.inj (actualMapped.symm.trans qMapped)
      subst index
      have nodeEq : current=qNode := Option.some.inj (present.symm.trans qAt)
      exact nodeEq ▸ qHidden
    · subst row
      rw [sameTag,←tagEq] at actualMapped
      have equal : index=child := Option.some.inj (actualMapped.symm.trans mapped)
      subst index
      have nodeEq : current=node := Option.some.inj (present.symm.trans childAt)
      exact nodeEq ▸ nodeHidden
  · dsimp only [CurrentCallEmptyEntryCompleteRelease.written]
    rw [capacity]
    exact bounds


def rootSource {options before tracker argument} (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument) : FrameState :=
  match effect.allocation with | none => {} | some id => ({} : FrameState).addProtector id tracker.global.nextPointerTag

private theorem boolTree_other {options before tracker argument} (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (id : AllocId) (tree : BorrowTree) (different : effect.allocation≠some id) : boolTree effect id tree=tree := by
  cases effect <;> simp_all [boolTree,CurrentCallEmptyTypedEntry.Effect.allocation]

private theorem root_complete_after_effect {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (ret : ReturnData before tracker place call) (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (sourceFrame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId) (valid : localId<sourceFrame.locals.size)
    (tree : BorrowTree) (treeEq : tree=boolTree effect ret.physical.id ret.physical.entry.allocation.extra)
    (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree (CurrentCallEmptyEntryArguments.nextTracker effect
      (CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources)).global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (node : TreeNode) (present : tree.nodes.get ret.pointer.grant=some node)
    (nodeTag : node.tag=ret.node.tag) (exposed : node.isExposed=ret.node.isExposed)
    (nodeRoom : tree.nodes.size+1≤4294967295) (short : tree.nodes.size+1<65536)
    (bounds : (UInt64.ofNat call.returnOffset).toNat+1≤tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion (CurrentCallEmptyEntryArguments.nextTracker effect
      (CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources)).global.protectedTags ret.pointer.grant)
      (UInt64.ofNat call.returnOffset) (UInt64.ofNat call.returnOffset+1) tree.locations) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    let current := (CurrentCallEmptyEntryArguments.nextTracker effect fresh).global
    Nonempty (RootOperation tree current (rootSource effect) ret.physical.id ret.pointer.value.provenance
      (UInt64.ofNat call.returnOffset) effect.allocation tracker.global.nextPointerTag (effect_tag_room input effect)) := by
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  let current := (CurrentCallEmptyEntryArguments.nextTracker effect fresh).global
  have oldTagBound := GeneralBorrowForestTagHighWater.mapped ret.physical.entry.allocation.extra tracker.global.protectedTags
    tracker.global.nextPointerTag ret.node.tag ret.runtime.below ret.pointer.grant
    (ret.runtime.formed.allocator.nodeTags ret.pointer.grant ret.node ret.present)
  have oldDifferent : ret.node.tag≠tracker.global.nextPointerTag := GeneralBorrowForestTagHighWater.different _ _ oldTagBound
  have freshMap : GeneralBorrowTagMap.Fresh ret.physical.entry.allocation.extra.tagMapping tracker.global.nextPointerTag := by
    intro row member;exact GeneralBorrowForestTagHighWater.different _ _ (ret.runtime.below.mapping row member)
  have oldAbsent : ret.physical.entry.allocation.extra.indexOfTag tracker.global.nextPointerTag=none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find _ _ freshMap,Option.map_none]
  have nextDifferent : current.nextPointerTag≠tracker.global.nextPointerTag := by
    have next := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
    have actual := effect_counter effect fresh
    change current.nextPointerTag=_ at actual
    intro equal
    rw [equal] at actual
    have values := congrArg (fun tag : BorTag => tag.value.toNat) actual
    omega
  have provenance : match ret.pointer.value.provenance with | .concrete _ tag => tag=node.tag | .wildcard => node.isExposed=true := by
    cases kind : ret.pointer.value.provenance with
    | concrete id tag => exact (show tag=ret.node.tag by simpa only [kind] using ret.provenance).trans nodeTag.symm
    | wildcard => exact exposed.trans (show ret.node.isExposed=true by simpa only [kind] using ret.provenance)
  apply rootOperation_complete tree current (rootSource effect) ret.physical.id completion runtime complete order ret.pointer node present
    provenance (effect_tag_room input effect) nodeRoom short (UInt64.ofNat call.returnOffset) bounds owned effect.allocation tracker.global.nextPointerTag
  · cases allocation : effect.allocation <;> simp only [rootSource,allocation] <;> rfl
  · intro same
    rw [treeEq]
    exact effect_source_leaf input effect #[] sourceFrame localId valid ret.physical.id ret.physical.entry ret.physical.live same
  · intro different
    rw [treeEq,boolTree_other effect ret.physical.id ret.physical.entry.allocation.extra different]
    exact oldAbsent
  · exact fun eq => oldDifferent (nodeTag.symm.trans eq)
  · exact nextDifferent

private theorem complete_fnentry_write (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (completion : Completion) (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    (pointer : PointerInstance) (node : TreeNode) (present : tree.nodes.get pointer.grant = some node)
    (provenance : match pointer.value.provenance with | .concrete _ tag => tag = node.tag | .wildcard => node.isExposed = true)
    (room : global.nextPointerTag.value < 18446744073709551615)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295) (short : tree.nodes.size+1 < 65536)
    (offset : UInt64) (bounds : offset.toNat+1 ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (Authority tree completion global.protectedTags pointer.grant) offset (offset+1) tree.locations) :
    ∃ output,CandidateCurrentFnEntryRaw.operation tree global frame allocation pointer.value.provenance offset 1 = .ok output ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      let written := output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes offset) (Size.ofBytes 1)
        .Write output.global.protectedTags .VisitChildrenOfAccessed
      written.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts written.tree output.global ∧
        written.tree.locations.size = tree.locations.size := by
  obtain ⟨borrow⟩ := CurrentCallEmptyEntryCompleteRelease.construct tree global frame allocation completion runtime complete order
    pointer node present provenance room nodeRoom short offset bounds owned
  exact ⟨borrow.output,borrow.actual,borrow.readCompleted,borrow.childCompleted,borrow.writeCompleted,borrow.writeRuntime,borrow.writeCapacity⟩


private theorem zero_rights_initial (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (completion : Completion) (held : ProtectedTags) (source : UniIndex) (lower upper : UInt64)
    (clean : GeneralBorrowFreshFutureClean.Clean tree slot.index)
    (owned : OwnedOn (Authority tree completion held source) lower upper tree.locations) :
    OwnedOn (ZeroRights tree slot tag completion held source) lower upper (slot.after tag).locations := by
  intro cursor valid positive start stop
  refine ⟨owned cursor valid positive start stop,?_⟩
  have empty : (slot.after tag).locations.entries[cursor].data.perms.get slot.index = none := clean cursor valid
  simp [empty,WildcardHitZeroConstructor.rootNode,TreeNode.defaultLocationState,OrdinaryBorrowAuthority.ForeignWrite,LocationState.possible,Permission.isUnique]

private theorem operation_after_effect {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (ret : ReturnData before tracker place call)
    (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument) (frame : FrameState) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    let global := (CurrentCallEmptyEntryArguments.nextTracker effect fresh).global
    let tree := boolTree effect ret.physical.id ret.physical.entry.allocation.extra
    let offset := UInt64.ofNat call.returnOffset
    ∃ output,CandidateCurrentFnEntryRaw.operation tree global frame ret.physical.id ret.pointer.value.provenance offset 1 = .ok output ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      let written := output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes offset) (Size.ofBytes 1)
        .Write output.global.protectedTags .VisitChildrenOfAccessed
      written.status = .Completed ∧ DuplicatePrefixBorrowContract.RuntimeFacts written.tree output.global ∧
        written.tree.locations.size = ret.physical.entry.allocation.extra.locations.size := by
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  let current := (CurrentCallEmptyEntryArguments.nextTracker effect fresh).global
  let original := ret.physical.entry.allocation.extra
  let offset := UInt64.ofNat call.returnOffset
  have currentRuntime := original_runtime_after_effect effect fresh original ret.runtime
  have currentOwned := original_owned_after_effect effect fresh original ret.runtime ret.precise.completion ret.pointer.grant offset (offset+1) ret.owned
  have room : current.nextPointerTag.value < 18446744073709551615 := effect_tag_room input effect
  have margin : original.nodes.size+16 < 65536 := input.machine.resources.nodeRoom (ret.physical.id,ret.physical.entry)
    (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some ret.physical.live))
  have initialRoom : original.nodes.size+1 ≤ 4294967295 := by omega
  have initialShort : original.nodes.size+1 < 65536 := by omega
  have unchanged := complete_fnentry_write original current frame ret.physical.id ret.precise.completion currentRuntime ret.completes ret.order
    ret.pointer ret.node ret.present ret.provenance room initialRoom initialShort offset ret.bounds currentOwned
  have freshTag : GeneralBorrowTagMap.Fresh original.tagMapping tracker.global.nextPointerTag :=
    (GeneralBorrowFnEntryRegistrationRuntime.prepare original tracker.global {} ret.physical.id fresh ret.runtime).2.2.2.2.2
  have tagBound : tracker.global.nextPointerTag.value.toNat < current.nextPointerTag.value.toNat := by
    have next := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
    have actual := effect_counter effect fresh
    change current.nextPointerTag = _ at actual
    rw [actual]
    omega
  cases effect with
  | integer | miss | concreteNonlive | wildcardNonlive | concreteImage | wildcardImage => exact unchanged
  | concreteLive address id parentTag entry nextTree live child =>
    by_cases same : id = ret.physical.id
    · subst id
      have entryEq : entry = ret.physical.entry := (Prod.mk.inj (Option.some.inj (live.symm.trans ret.physical.live))).2
      subst entry
      simp only [boolTree]
      have candidate := CurrentCallEmptyTypedEntryInteger.empty_candidate input
      change address ≠ 0 ∧ DuplicatePrefixEmptyReferenceInput.Concrete (DuplicatePrefixCallSpecification.imageContext options before tracker)
        before.memory before.user.addresses ret.physical.id parentTag at candidate
      have parentInput : DuplicatePrefixEmptyReferenceInput.Parent original (some parentTag) := by
        rcases ConcreteEmptyCandidateDispatch.target_cases _ _ _ ret.physical.id parentTag candidate.2.2 with liveCase | nonlive | image
        · obtain ⟨old,found,parent⟩ := liveCase
          have oldEq := congrArg Prod.snd (Option.some.inj (found.symm.trans ret.physical.live))
          dsimp only at oldEq
          subst old
          exact parent
        · rw [ret.physical.live] at nonlive
          cases nonlive.2
        · obtain ⟨_,_,absent,_⟩ := image
          rw [ret.physical.live] at absent
          cases absent
      obtain ⟨parent,parentNode,tagged,parentAt⟩ := parentInput
      have heldLookup : current.protectedTags.get tracker.global.nextPointerTag = some .StrongProtector :=
        (GeneralBorrowFnEntryRegistrationRuntime.prepare original tracker.global {} ret.physical.id fresh ret.runtime).2.1
      have held : current.protectedTags.contains tracker.global.nextPointerTag = true := by unfold ProtectedTags.contains;rw [heldLookup];rfl
      have older := GeneralBorrowParentTagInvariant.parent_below_fresh original tracker.global ret.runtime parent parentNode parentAt
      obtain ⟨base,sourceOffset,cached,addressEq,sourceStep⟩ := child
      have sourceResult := CurrentCallEmptyEntryConcreteZero.construct original current ret.precise.completion currentRuntime ret.completes ret.order
        parentTag tracker.global.nextPointerTag parent parentNode tagged parentAt freshTag initialRoom tagBound held
        (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp older))) sourceOffset
        ret.pointer.grant ret.node ret.present offset (offset+1) currentOwned
      rw [sourceStep] at sourceResult
      dsimp only at sourceResult
      obtain ⟨_,nextRuntime,capacity,growth,sourceChild,_,completed,ordered,owned,nextNode,nextAt,nodeTag,nodeExposed⟩ := sourceResult
      have provenance : match ret.pointer.value.provenance with | .concrete _ tag => tag = nextNode.tag | .wildcard => nextNode.isExposed = true := by
        cases kind : ret.pointer.value.provenance with
        | concrete id tag => exact (show tag = ret.node.tag by simpa only [kind] using ret.provenance).trans nodeTag.symm
        | wildcard => exact nodeExposed.trans (show ret.node.isExposed = true by simpa only [kind] using ret.provenance)
      have afterShort : nextTree.nodes.size+1 < 65536 := by omega
      have afterRoom : nextTree.nodes.size+1 ≤ 4294967295 := by omega
      have afterBounds : offset.toNat+1 ≤ nextTree.locations.size.bytes.toNat := by rw [capacity];exact ret.bounds
      obtain ⟨output,operation,readDone,childDone,writeDone,writtenRuntime,writtenCapacity⟩ := complete_fnentry_write nextTree current frame ret.physical.id
        (S05ConcreteProtectedChildCompletion.extend ret.precise.completion sourceChild parent) nextRuntime completed ordered ret.pointer nextNode nextAt provenance
        room afterRoom afterShort offset afterBounds owned
      exact ⟨output,operation,readDone,childDone,writeDone,writtenRuntime,writtenCapacity.trans capacity⟩
    · simpa only [boolTree,ite_eq_right same] using unchanged
  | wildcardLive address hit entry nextTree live child =>
    by_cases same : hit.id = ret.physical.id
    · have liveAtBool : before.memory.live.find? (fun row => row.1 == ret.physical.id) = some (ret.physical.id,entry) := by simpa only [same] using live
      have entryEq : entry = ret.physical.entry := (Prod.mk.inj (Option.some.inj (liveAtBool.symm.trans ret.physical.live))).2
      subst entry
      obtain ⟨slot,treeEq⟩ := child
      subst nextTree
      simp only [boolTree,ite_eq_left same]
      have heldLookup : current.protectedTags.get tracker.global.nextPointerTag = some .StrongProtector :=
        (GeneralBorrowFnEntryRegistrationRuntime.prepare original tracker.global {} hit.id fresh ret.runtime).2.1
      have held : current.protectedTags.contains tracker.global.nextPointerTag = true := by unfold ProtectedTags.contains;rw [heldLookup];rfl
      have sourceResult := S04ZeroWildcardRuntime.construct original current currentRuntime tracker.global.nextPointerTag freshTag initialRoom tagBound held 0
      rw [slot.child tracker.global.nextPointerTag freshTag 0] at sourceResult
      have nextRuntime := sourceResult.2.1
      have nextOrder := zero_slot_order original slot tracker.global.nextPointerTag ret.precise.completion ret.completes ret.order
      have distinct := zero_slot_distinct original slot tracker.global.nextPointerTag ret.precise.completion ret.completes
      have growth : (slot.after tracker.global.nextPointerTag).nodes.size ≤ original.nodes.size+1 := sourceResult.2.2.2
      have afterShort : (slot.after tracker.global.nextPointerTag).nodes.size+1 < 65536 := by omega
      have afterRoom : (slot.after tracker.global.nextPointerTag).nodes.size+1 ≤ 4294967295 := by omega
      have clean := DuplicatePrefixBorrowContract.vacant_clean ret.runtime slot.index slot.vacant
      obtain ⟨depth⟩ := ret.runtime.formed.depth
      obtain ⟨position,root,rootNode,rootAt,rootPresent,path⟩ := CandidateCurrentWindowAuthority.root_path original ret.runtime.formed.toGraphState
        ret.pointer.grant ret.node ret.present
      cases kind : ret.pointer.value.provenance with
      | concrete supplied pointerTag =>
        have pointerTagEq : pointerTag = ret.node.tag := by simpa only [kind] using ret.provenance
        have zeroOwned := zero_rights_initial original slot tracker.global.nextPointerTag ret.precise.completion current.protectedTags ret.pointer.grant offset (offset+1) clean currentOwned
        obtain ⟨output,operation,_,_,_,_,_,readDone,childDone,writeDone,writtenRuntime,_,capacity⟩ := zero_fnentry_write original slot tracker.global.nextPointerTag
          ret.precise.completion current frame ret.physical.id ret.completes ret.runtime.formed.toGraphState depth ret.order nextOrder distinct nextRuntime
          position root ret.pointer.grant rootNode ret.node rootAt rootPresent ret.present path room afterRoom clean offset 1 (by decide) ret.bounds zeroOwned afterShort
        refine ⟨output,?_,readDone,childDone,writeDone,writtenRuntime,capacity⟩
        simpa only [CandidateCurrentFnEntryRaw.operation,kind,pointerTagEq] using operation
      | wildcard =>
        have exposed : ret.node.isExposed = true := by simpa only [kind] using ret.provenance
        have older := GeneralBorrowParentTagInvariant.parent_below_fresh original tracker.global ret.runtime ret.pointer.grant ret.node ret.present
        have completed := zero_completes_of_exposed_return original slot tracker.global.nextPointerTag ret.precise.completion current ret.completes nextRuntime
          ret.pointer.grant ret.node ret.present exposed older position root rootAt path
        have owned := zero_root_owned original slot tracker.global.nextPointerTag ret.precise.completion current.protectedTags ret.completes ret.pointer.grant
          ⟨ret.node,ret.present⟩ offset (offset+1) clean currentOwned
        have nextAt : (slot.after tracker.global.nextPointerTag).nodes.get ret.pointer.grant = some ret.node :=
          S04ZeroRootObserverNormal.old_node original slot tracker.global.nextPointerTag ret.pointer.grant ret.node ret.present
        obtain ⟨output,operation,readDone,childDone,writeDone,writtenRuntime,capacity⟩ := complete_fnentry_write
          (slot.after tracker.global.nextPointerTag) current frame ret.physical.id
          (S05ConcreteProtectedChildCompletion.extend ret.precise.completion slot.index ret.pointer.grant) nextRuntime completed nextOrder ret.pointer ret.node nextAt
          (by simpa only [kind] using exposed) room afterRoom afterShort offset ret.bounds owned
        refine ⟨output,?_,readDone,childDone,writeDone,writtenRuntime,?_⟩
        · simpa only [kind] using operation
        · exact capacity.trans (show (slot.after tracker.global.nextPointerTag).locations.size = ret.physical.entry.allocation.extra.locations.size from rfl)
    · simpa only [boolTree,ite_eq_right same] using unchanged

private theorem rootOperation_after_effect {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (ret : ReturnData before tracker place call)
    (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (sourceFrame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId) (valid : localId<sourceFrame.locals.size) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    let current := (CurrentCallEmptyEntryArguments.nextTracker effect fresh).global
    Nonempty (RootOperation (boolTree effect ret.physical.id ret.physical.entry.allocation.extra) current
      (rootSource effect) ret.physical.id ret.pointer.value.provenance (UInt64.ofNat call.returnOffset)
      effect.allocation tracker.global.nextPointerTag (effect_tag_room input effect)) := by
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  let current := (CurrentCallEmptyEntryArguments.nextTracker effect fresh).global
  let original := ret.physical.entry.allocation.extra
  let offset := UInt64.ofNat call.returnOffset
  have currentRuntime := original_runtime_after_effect effect fresh original ret.runtime
  have currentOwned := original_owned_after_effect effect fresh original ret.runtime ret.precise.completion ret.pointer.grant offset (offset+1) ret.owned
  have room : current.nextPointerTag.value < 18446744073709551615 := effect_tag_room input effect
  have margin : original.nodes.size+16 < 65536 := input.machine.resources.nodeRoom (ret.physical.id,ret.physical.entry)
    (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some ret.physical.live))
  have initialRoom : original.nodes.size+1 ≤ 4294967295 := by omega
  have initialShort : original.nodes.size+1 < 65536 := by omega
  have unchanged (sameTree : boolTree effect ret.physical.id original=original) :
      Nonempty (RootOperation original current (rootSource effect) ret.physical.id ret.pointer.value.provenance offset
        effect.allocation tracker.global.nextPointerTag room) :=
    root_complete_after_effect input ret effect sourceFrame localId valid original sameTree.symm ret.precise.completion
      currentRuntime ret.completes ret.order ret.node ret.present rfl rfl initialRoom initialShort ret.bounds currentOwned
  have freshTag : GeneralBorrowTagMap.Fresh original.tagMapping tracker.global.nextPointerTag :=
    (GeneralBorrowFnEntryRegistrationRuntime.prepare original tracker.global {} ret.physical.id fresh ret.runtime).2.2.2.2.2
  have tagBound : tracker.global.nextPointerTag.value.toNat < current.nextPointerTag.value.toNat := by
    have next := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
    have actual := effect_counter effect fresh
    change current.nextPointerTag = _ at actual
    rw [actual]
    omega
  cases effect with
  | integer | miss | concreteNonlive | wildcardNonlive | concreteImage | wildcardImage => exact unchanged rfl
  | concreteLive address id parentTag entry nextTree live child =>
    by_cases same : id = ret.physical.id
    · subst id
      have entryEq : entry = ret.physical.entry := (Prod.mk.inj (Option.some.inj (live.symm.trans ret.physical.live))).2
      subst entry
      simp only [boolTree]
      have candidate := CurrentCallEmptyTypedEntryInteger.empty_candidate input
      change address ≠ 0 ∧ DuplicatePrefixEmptyReferenceInput.Concrete (DuplicatePrefixCallSpecification.imageContext options before tracker)
        before.memory before.user.addresses ret.physical.id parentTag at candidate
      have parentInput : DuplicatePrefixEmptyReferenceInput.Parent original (some parentTag) := by
        rcases ConcreteEmptyCandidateDispatch.target_cases _ _ _ ret.physical.id parentTag candidate.2.2 with liveCase | nonlive | image
        · obtain ⟨old,found,parent⟩ := liveCase
          have oldEq := congrArg Prod.snd (Option.some.inj (found.symm.trans ret.physical.live))
          dsimp only at oldEq
          subst old
          exact parent
        · rw [ret.physical.live] at nonlive
          cases nonlive.2
        · obtain ⟨_,_,absent,_⟩ := image
          rw [ret.physical.live] at absent
          cases absent
      obtain ⟨parent,parentNode,tagged,parentAt⟩ := parentInput
      have heldLookup : current.protectedTags.get tracker.global.nextPointerTag = some .StrongProtector :=
        (GeneralBorrowFnEntryRegistrationRuntime.prepare original tracker.global {} ret.physical.id fresh ret.runtime).2.1
      have held : current.protectedTags.contains tracker.global.nextPointerTag = true := by unfold ProtectedTags.contains;rw [heldLookup];rfl
      have older := GeneralBorrowParentTagInvariant.parent_below_fresh original tracker.global ret.runtime parent parentNode parentAt
      obtain ⟨base,sourceOffset,cached,addressEq,sourceStep⟩ := child
      have sourceResult := CurrentCallEmptyEntryConcreteZero.construct original current ret.precise.completion currentRuntime ret.completes ret.order
        parentTag tracker.global.nextPointerTag parent parentNode tagged parentAt freshTag initialRoom tagBound held
        (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp older))) sourceOffset
        ret.pointer.grant ret.node ret.present offset (offset+1) currentOwned
      rw [sourceStep] at sourceResult
      dsimp only at sourceResult
      obtain ⟨_,nextRuntime,capacity,growth,sourceChild,_,completed,ordered,owned,nextNode,nextAt,nodeTag,nodeExposed⟩ := sourceResult
      have provenance : match ret.pointer.value.provenance with | .concrete _ tag => tag = nextNode.tag | .wildcard => nextNode.isExposed = true := by
        cases kind : ret.pointer.value.provenance with
        | concrete id tag => exact (show tag = ret.node.tag by simpa only [kind] using ret.provenance).trans nodeTag.symm
        | wildcard => exact nodeExposed.trans (show ret.node.isExposed = true by simpa only [kind] using ret.provenance)
      have afterShort : nextTree.nodes.size+1 < 65536 := by omega
      have afterRoom : nextTree.nodes.size+1 ≤ 4294967295 := by omega
      have afterBounds : offset.toNat+1 ≤ nextTree.locations.size.bytes.toNat := by rw [capacity];exact ret.bounds
      exact root_complete_after_effect input ret _ sourceFrame localId valid nextTree (by simp only [boolTree,ite_true])
        (S05ConcreteProtectedChildCompletion.extend ret.precise.completion sourceChild parent) nextRuntime completed ordered
        nextNode nextAt nodeTag nodeExposed afterRoom afterShort afterBounds owned
    · simpa only [boolTree,ite_eq_right same] using unchanged (by simp only [boolTree,ite_eq_right same])
  | wildcardLive address hit entry nextTree live child =>
    by_cases same : hit.id = ret.physical.id
    · have liveAtBool : before.memory.live.find? (fun row => row.1 == ret.physical.id) = some (ret.physical.id,entry) := by simpa only [same] using live
      have entryEq : entry = ret.physical.entry := (Prod.mk.inj (Option.some.inj (liveAtBool.symm.trans ret.physical.live))).2
      subst entry
      obtain ⟨slot,treeEq⟩ := child
      subst nextTree
      simp only [boolTree,ite_eq_left same]
      have heldLookup : current.protectedTags.get tracker.global.nextPointerTag = some .StrongProtector :=
        (GeneralBorrowFnEntryRegistrationRuntime.prepare original tracker.global {} hit.id fresh ret.runtime).2.1
      have held : current.protectedTags.contains tracker.global.nextPointerTag = true := by unfold ProtectedTags.contains;rw [heldLookup];rfl
      have sourceResult := S04ZeroWildcardRuntime.construct original current currentRuntime tracker.global.nextPointerTag freshTag initialRoom tagBound held 0
      rw [slot.child tracker.global.nextPointerTag freshTag 0] at sourceResult
      have nextRuntime := sourceResult.2.1
      have nextOrder := zero_slot_order original slot tracker.global.nextPointerTag ret.precise.completion ret.completes ret.order
      have distinct := zero_slot_distinct original slot tracker.global.nextPointerTag ret.precise.completion ret.completes
      have growth : (slot.after tracker.global.nextPointerTag).nodes.size ≤ original.nodes.size+1 := sourceResult.2.2.2
      have afterShort : (slot.after tracker.global.nextPointerTag).nodes.size+1 < 65536 := by omega
      have afterRoom : (slot.after tracker.global.nextPointerTag).nodes.size+1 ≤ 4294967295 := by omega
      have clean := DuplicatePrefixBorrowContract.vacant_clean ret.runtime slot.index slot.vacant
      obtain ⟨depth⟩ := ret.runtime.formed.depth
      obtain ⟨position,root,rootNode,rootAt,rootPresent,path⟩ := CandidateCurrentWindowAuthority.root_path original ret.runtime.formed.toGraphState
        ret.pointer.grant ret.node ret.present
      cases kind : ret.pointer.value.provenance with
      | concrete supplied pointerTag =>
        have pointerTagEq : pointerTag = ret.node.tag := by simpa only [kind] using ret.provenance
        have zeroOwned := zero_rights_initial original slot tracker.global.nextPointerTag ret.precise.completion current.protectedTags ret.pointer.grant offset (offset+1) clean currentOwned
        let actualEffect := CurrentCallEmptyTypedEntry.Effect.wildcardLive address hit ret.physical.entry
          (slot.after tracker.global.nextPointerTag) live ⟨slot,rfl⟩
        have actual := rootOperation_of_zero original slot tracker.global.nextPointerTag ret.precise.completion current
          (rootSource actualEffect) ret.physical.id supplied ret.completes ret.runtime.formed.toGraphState depth ret.order nextOrder distinct nextRuntime
          position root ret.pointer.grant rootNode ret.node rootAt rootPresent ret.present path room afterRoom clean offset ret.bounds zeroOwned afterShort
          (by change #[(hit.id,tracker.global.nextPointerTag)]=_;rw [same])
        simpa only [actualEffect,CurrentCallEmptyTypedEntry.Effect.allocation,same,kind,pointerTagEq] using actual
      | wildcard =>
        have exposed : ret.node.isExposed = true := by simpa only [kind] using ret.provenance
        have older := GeneralBorrowParentTagInvariant.parent_below_fresh original tracker.global ret.runtime ret.pointer.grant ret.node ret.present
        have completed := zero_completes_of_exposed_return original slot tracker.global.nextPointerTag ret.precise.completion current ret.completes nextRuntime
          ret.pointer.grant ret.node ret.present exposed older position root rootAt path
        have owned := zero_root_owned original slot tracker.global.nextPointerTag ret.precise.completion current.protectedTags ret.completes ret.pointer.grant
          ⟨ret.node,ret.present⟩ offset (offset+1) clean currentOwned
        have nextAt : (slot.after tracker.global.nextPointerTag).nodes.get ret.pointer.grant = some ret.node :=
          S04ZeroRootObserverNormal.old_node original slot tracker.global.nextPointerTag ret.pointer.grant ret.node ret.present
        simpa only [kind] using root_complete_after_effect input ret _ sourceFrame localId valid (slot.after tracker.global.nextPointerTag)
          (by simp only [boolTree,ite_eq_left same])
          (S05ConcreteProtectedChildCompletion.extend ret.precise.completion slot.index ret.pointer.grant)
          nextRuntime completed nextOrder ret.node nextAt rfl rfl afterRoom afterShort ret.bounds owned
    · simpa only [boolTree,ite_eq_right same] using unchanged (by simp only [boolTree,ite_eq_right same])

/-- Internal operation-to-typed consumer. Its certificates are produced by the
finite empty-effect dispatcher, never requested from the caller. -/
private theorem protect_from_operation (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualRetagContext.Context options remaining span)
    (machine : Before) (tracker : MachineHooks.BorrowState) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker = some tracker) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place)
    (offset : Nat) (offsetEq : physical.offset = UInt64.ofNat offset)
    (binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id offset 1)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (ghost : machine.user.payload.ghost = false) (race : machine.dataRace = none)
    (backend : machine.user.payload.payload.user.backend = .none)
    (ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1)
    (output : GeneralBorrowForestFnEntry.Output)
    (operation : CandidateCurrentFnEntryRaw.operation physical.entry.allocation.extra tracker.global borrowFrame physical.id
      physical.pointer.provenance (UInt64.ofNat offset) 1 = .ok output)
    (readDone : output.access.status = .Completed) (childDone : output.child.outcome = .ok ())
    (writeDone : (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes 1)
      .Write output.global.protectedTags .VisitChildrenOfAccessed).status = .Completed) :
    ∃ updated : Allocation Provenance BorrowTree,
    let retagged := ReturnProtection.borrowedState frames frame borrowFrame machine tracker room physical.id physical.entry output.child.tree
    let final := {retagged with machine := {retagged.machine with memory := {retagged.machine.memory with live :=
      ((retagged.machine.memory.live.filter fun row => row.1 != physical.id).push (physical.id,{physical.entry with allocation := updated}))}}}
    (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place (Storage.withCurrent frames frame machine) = .ok () final ∧
      updated.extra = (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes 1)
        .Write output.global.protectedTags .VisitChildrenOfAccessed).tree ∧
      updated.byteSize = physical.entry.allocation.byteSize ∧ updated.len = physical.entry.allocation.len ∧
      AllocationCopy.snapshot updated = AllocationCopy.snapshot physical.entry.allocation ∧
      CurrentCallBoolProtection.WindowReady final.machine physical.id physical.offset.toNat 1 ∧
      Allocation.writeUninit (allocRange (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes 1)) (Size.ofBytes 8)
        (physical.entry.allocation.setExtra (CurrentCallEmptyEntryCompleteRelease.written output (UInt64.ofNat offset)).tree) = .ok () updated := by
  have outputEq : output = CurrentCallTypedFnEntry.literal physical.entry.allocation.extra tracker.global borrowFrame physical.id room
      physical.pointer.provenance (UInt64.ofNat offset) 1 := Except.ok.inj (operation.symm.trans
    (CurrentCallTypedFnEntry.literal_operation physical.entry.allocation.extra tracker.global borrowFrame physical.id room
      physical.pointer.provenance (UInt64.ofNat offset) 1))
  have tagEq : output.tag = tracker.global.nextPointerTag := by rw [outputEq];rfl
  have readEq : physical.entry.allocation.extra.performBorrowAccessRange (CandidateCurrentWindowPointerChecks.extraOf physical.pointer.provenance)
      (Size.ofBytes (UInt64.ofNat offset)) (Size.ofBytes 1) .Read
      (registeredGlobal (allocatedTracker tracker room) tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed = output.access := by
    rw [outputEq]
    rfl
  have childEq : output.access.tree.newChild (Size.ofBytes (UInt64.ofNat offset))
      (CandidateCurrentWindowPointerChecks.extraOf physical.pointer.provenance) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 1) ChildBorrow.fnEntryLocation) MachineHooks.protectionPolicy.outsidePermission
      MachineHooks.protectionPolicy.protector.isSome = output.child := by rw [outputEq];rfl
  have childStep : output.access.tree.newChild (Size.ofBytes (UInt64.ofNat offset))
      (CandidateCurrentWindowPointerChecks.extraOf physical.pointer.provenance) tracker.global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes 1) ChildBorrow.fnEntryLocation) MachineHooks.protectionPolicy.outsidePermission
      MachineHooks.protectionPolicy.protector.isSome = ⟨output.child.tree,.ok ()⟩ := by
    rw [childEq]
    cases h : output.child with
    | mk tree outcome =>
      rw [h] at childDone
      dsimp only at childDone
      cases childDone
      rfl
  have retag := CurrentCallBoolProtection.retag_of_steps options remaining span ctx limits.retag machine tracker frames frame borrowFrame enabled frameBorrow
    place physical.layout physical.pointer physical.physicalPointer physical.id offset binding physical.entry physical.live room race
    output.access.tree output.child.tree (congrArg BorrowTree.BorrowTreeAccessResult.tree readEq) (by rw [readEq];exact readDone) childStep
  let retagged := ReturnProtection.borrowedState frames frame borrowFrame machine tracker room physical.id physical.entry output.child.tree
  let childWindow := CurrentCallBoolWindow.protected_window physical frames frame borrowFrame tracker room output.child.tree
  have tracked : retagged.machine.borrowTracker = some ⟨output.global,tracker.retagMode⟩ := by rw [outputEq];rfl
  obtain ⟨sync,extraAt,outside⟩ := ready
  have childExtra : retagged.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == childWindow.id) =
      some (childWindow.id,⟨none,sync⟩) := extraAt
  have concrete : childWindow.pointer.provenance = .concrete childWindow.id tracker.global.nextPointerTag := rfl
  have completed : (childWindow.entry.allocation.extra.performBorrowAccessRange (.concrete tracker.global.nextPointerTag)
      (Size.ofBytes childWindow.offset) (Size.ofBytes 1) .Write output.global.protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    simpa only [childWindow,CurrentCallBoolWindow.protected_window,CurrentCallBoolWindow.retagged,CurrentCallBoolWindow.tree_only,
      Allocation.setExtra,Allocation.mapExtra,offsetEq,tagEq] using writeDone
  obtain ⟨updated,write,extra,byteSize,length,_,mutation⟩ := CurrentCallBoolProtection.write_uninit_concrete options remaining span ctx retagged
    (TypedRetagGeneric.retaggedPlace place physical.id tracker.global.nextPointerTag) childWindow ⟨output.global,tracker.retagMode⟩ tracked
    tracker.global.nextPointerTag concrete ghost race backend sync childExtra outside completed
  refine ⟨updated,?_,?_,byteSize,length,?_,?_,?_⟩
  · change TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag limits.retag place (Storage.withCurrent frames frame machine) = _
    unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
    simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,Storage.withCurrent,enabled,Option.isSome_some,ite_true]
    erw [retag]
    exact write
  · simpa only [childWindow,CurrentCallBoolWindow.protected_window,CurrentCallBoolWindow.retagged,CurrentCallBoolWindow.tree_only,
      Allocation.setExtra,Allocation.mapExtra,offsetEq,tagEq] using extra
  · have preserved := CurrentCallBoolProtection.uninit_snapshot _ updated _ _ mutation
    exact preserved
  · exact (show CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1 from ⟨sync,extraAt,outside⟩).transport rfl


  · simpa only [childWindow,CurrentCallBoolWindow.protected_window,CurrentCallBoolWindow.retagged,CurrentCallBoolWindow.tree_only,
      Allocation.setExtra,Allocation.mapExtra,offsetEq,tagEq,CurrentCallEmptyEntryCompleteRelease.written] using mutation

def afterArgumentsTracker {options before tracker argument} (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) : MachineHooks.BorrowState :=
  {(CurrentCallEmptyEntryArguments.nextTracker effect fresh) with retagMode := tracker.retagMode}
def afterArgumentsMachine {options before tracker argument} (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size) : Before :=
  {(CurrentCallEmptyTypedEntry.resultMachine effect fresh remaining span frames frame borrowFrame localId valid) with
    borrowTracker := some (afterArgumentsTracker effect fresh)}

private theorem protect_after_effect {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (ret : ReturnData before tracker place call) (readiness : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (ctx : ActualRetagContext.Context options (remaining+1) span)
    (frames : Array CompilerFrameContext.ActualFrame) (sourceFrame : CompilerFrameContext.ActualFrame) (sourceBorrow : FrameState)
    (localId : MIR.LocalId) (valid : localId < sourceFrame.locals.size)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    let machine := afterArgumentsMachine effect fresh remaining span frames sourceFrame sourceBorrow localId valid
    let currentTracker := afterArgumentsTracker effect fresh
    ∃ physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place,
    ∃ room : currentTracker.global.nextPointerTag.value < 18446744073709551615,
    ∃ output : GeneralBorrowForestFnEntry.Output,∃ updated : Allocation Provenance BorrowTree,
      physical.id = call.returnId ∧ physical.pointer = ret.pointer.value ∧ physical.offset = UInt64.ofNat call.returnOffset ∧
      let retagged := ReturnProtection.borrowedState frames frame borrowFrame machine currentTracker room physical.id physical.entry output.child.tree
      let finalMachine : Before := {retagged.machine with memory := {retagged.machine.memory with live :=
        ((retagged.machine.memory.live.filter fun row => row.1 != physical.id).push (physical.id,{physical.entry with allocation := updated}))}}
      (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place (Storage.withCurrent frames frame machine) =
        .ok () (Storage.withCurrent frames (registeredFrame frame borrowFrame physical.id currentTracker.global.nextPointerTag) finalMachine) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts updated.extra output.global ∧
      CurrentCallBoolProtection.ProfileMemoryReadiness finalMachine call ∧
      CandidateCallBindings.WindowBinding finalMachine physical.pointer call.returnId call.returnOffset 1 ∧
      updated.byteSize = physical.entry.allocation.byteSize ∧ updated.len = physical.entry.allocation.len ∧
      AllocationCopy.snapshot updated = AllocationCopy.snapshot physical.entry.allocation ∧
      DuplicatePrefixTypeCacheOrigins.Origins finalMachine.user.payload.payload.user.types := by
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  let base := CurrentCallEmptyTypedEntry.resultMachine effect fresh remaining span frames sourceFrame sourceBorrow localId valid
  let machine := afterArgumentsMachine effect fresh remaining span frames sourceFrame sourceBorrow localId valid
  let currentTracker := afterArgumentsTracker effect fresh
  obtain ⟨oldPhysical,idEq,pointerEq,offsetEq,treeEq⟩ := physical_after_effect effect fresh remaining span frames sourceFrame sourceBorrow localId valid ret.physical
  let physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place := {oldPhysical with}
  have physicalId : physical.id = call.returnId := idEq.trans ret.id
  have physicalPointer : physical.pointer = ret.pointer.value := pointerEq.trans ret.pointerEq
  have physicalOffset : physical.offset = UInt64.ofNat call.returnOffset := offsetEq.trans ret.offset
  have enabled : machine.borrowTracker = some currentTracker := rfl
  have room : currentTracker.global.nextPointerTag.value < 18446744073709551615 := effect_tag_room input effect
  have binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id call.returnOffset 1 := by
    change CandidateCallBindings.WindowBinding base oldPhysical.pointer oldPhysical.id call.returnOffset 1
    rw [idEq,ret.id,pointerEq,ret.pointerEq]
    exact binding_after_effect effect fresh remaining span frames sourceFrame sourceBorrow localId valid ret.pointer.value call.returnId call.returnOffset 1 ret.binding
  have ghost : machine.user.payload.ghost = false := (CurrentCallEmptyEntryArguments.result_settings effect fresh remaining span frames sourceFrame sourceBorrow
    localId valid input.machine.settings.ghostOff).1
  have race : machine.dataRace = none := (CurrentCallEmptyTypedEntry.resultMachine_data effect fresh remaining span frames sourceFrame sourceBorrow localId valid).2.2.1.trans input.machine.settings.noDataRace
  have backend : machine.user.payload.payload.user.backend = .none := by
    have same : base.user.payload.payload.user.backend = before.user.payload.payload.user.backend := by cases effect <;> rfl
    exact same.trans input.machine.settings.noBackend
  have readyBefore : CurrentCallBoolProtection.WindowReady before ret.physical.id ret.physical.offset.toNat 1 := by
    rw [ret.id,ret.offsetNat]
    exact readiness.bool
  have ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1 := by
    change CurrentCallBoolProtection.WindowReady base oldPhysical.id oldPhysical.offset.toNat 1
    rw [idEq,offsetEq]
    exact window_ready_after_effect effect fresh remaining span frames sourceFrame sourceBorrow localId valid ret.physical.id ret.physical.entry
      ret.physical.live ret.physical.offset.toNat 1 readyBefore
  obtain ⟨output,operation,readDone,childDone,writeDone,writtenRuntime,_⟩ := operation_after_effect input ret effect borrowFrame
  have actualOperation : CandidateCurrentFnEntryRaw.operation physical.entry.allocation.extra currentTracker.global borrowFrame physical.id
      physical.pointer.provenance (UInt64.ofNat call.returnOffset) 1 = .ok output := by
    change CandidateCurrentFnEntryRaw.operation oldPhysical.entry.allocation.extra
      (CurrentCallEmptyEntryArguments.nextTracker effect fresh).global borrowFrame oldPhysical.id oldPhysical.pointer.provenance (UInt64.ofNat call.returnOffset) 1 = .ok output
    rw [treeEq,idEq,pointerEq,ret.pointerEq]
    exact operation
  obtain ⟨updated,protect,extra,byteSize,length,snapshot,readyAfter,_⟩ := protect_from_operation options limits (remaining+1) span ctx machine currentTracker frames frame borrowFrame
    enabled frameBorrow place physical call.returnOffset physicalOffset binding room ghost race backend ready output actualOperation readDone childDone writeDone
  let retagged := ReturnProtection.borrowedState frames frame borrowFrame machine currentTracker room physical.id physical.entry output.child.tree
  let finalMachine : Before := {retagged.machine with memory := {retagged.machine.memory with live :=
    ((retagged.machine.memory.live.filter fun row => row.1 != physical.id).push (physical.id,{physical.entry with allocation := updated}))}}
  have finalBinding : CandidateCallBindings.WindowBinding finalMachine physical.pointer call.returnId call.returnOffset 1 := by
    have original : CandidateCallBindings.WindowBinding machine physical.pointer call.returnId call.returnOffset 1 := by rw [←physicalId];exact binding
    apply CurrentCallBoolWindow.replace_binding machine finalMachine physical.pointer call.returnId call.returnOffset 1 original physical.id physical.entry
      {physical.entry with allocation := updated} physical.live length byteSize rfl
    exact congrArg (fun memory => memory.live) (MemoryCopyBridge.live_update_twice machine.memory physical.id
      {physical.entry with allocation := physical.entry.allocation.setExtra output.child.tree} {physical.entry with allocation := updated})
  have finalReady : CurrentCallBoolProtection.ProfileMemoryReadiness finalMachine call := by
    refine ⟨?_,?_⟩
    · intro positive
      have length := input.actual.length
      change call.length = 0 at length
      omega
    · have offsetNat : physical.offset.toNat = call.returnOffset := by rw [physicalOffset];exact (ret.offset ▸ ret.offsetNat)
      have finalWindow : CurrentCallBoolProtection.WindowReady finalMachine physical.id physical.offset.toNat 1 := readyAfter
      rw [physicalId,offsetNat] at finalWindow
      exact finalWindow
  have origins : DuplicatePrefixTypeCacheOrigins.Origins finalMachine.user.payload.payload.user.types := by
    have same : finalMachine.user.payload.payload.user.types = before.user.payload.payload.user.types :=
      (CurrentCallEmptyTypedEntry.resultMachine_data effect fresh remaining span frames sourceFrame sourceBorrow localId valid).2.1
    rw [same]
    exact input.machine.cacheOrigins
  refine ⟨physical,room,output,updated,physicalId,physicalPointer,physicalOffset,protect,?_,finalReady,finalBinding,byteSize,length,snapshot,origins⟩
  rw [extra]
  exact writtenRuntime


theorem protect_root_after_arguments {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (readiness : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (ctx : ActualRetagContext.Context options (remaining+1) span)
    (frames : Array CompilerFrameContext.ActualFrame) (sourceFrame : CompilerFrameContext.ActualFrame) (sourceBorrow : FrameState)
    (localId : MIR.LocalId) (valid : localId < sourceFrame.locals.size)
    (frame : CompilerFrameContext.ActualFrame) (frameBorrow : frame.extra.borrowTracker = some (rootSource effect)) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    let machine := afterArgumentsMachine effect fresh remaining span frames sourceFrame sourceBorrow localId valid
    let currentTracker := afterArgumentsTracker effect fresh
    ∃ physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place,
    ∃ room : currentTracker.global.nextPointerTag.value < 18446744073709551615,
    ∃ output : GeneralBorrowForestFnEntry.Output,
    ∃ certificate : RootOperation physical.entry.allocation.extra currentTracker.global (rootSource effect) physical.id
      physical.pointer.provenance (UInt64.ofNat call.returnOffset) effect.allocation tracker.global.nextPointerTag room,
    certificate.output=output ∧ ∃ updated : Allocation Provenance BorrowTree,
      physical.id = call.returnId ∧ physical.offset = UInt64.ofNat call.returnOffset ∧ physical.offset.toNat=call.returnOffset ∧
      let retagged := ReturnProtection.borrowedState frames frame (rootSource effect) machine currentTracker room physical.id physical.entry output.child.tree
      let finalMachine : Before := {retagged.machine with memory := {retagged.machine.memory with live :=
        ((retagged.machine.memory.live.filter fun row => row.1 != physical.id).push (physical.id,{physical.entry with allocation := updated}))}}
      (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place (Storage.withCurrent frames frame machine) =
        .ok () (Storage.withCurrent frames (registeredFrame frame (rootSource effect) physical.id currentTracker.global.nextPointerTag) finalMachine) ∧
      updated.extra = (CurrentCallEmptyEntryCompleteRelease.written output (UInt64.ofNat call.returnOffset)).tree ∧
      DuplicatePrefixBorrowContract.RuntimeFacts updated.extra output.global ∧
      CurrentCallBoolProtection.ProfileMemoryReadiness finalMachine call ∧
      CandidateCallBindings.WindowBinding finalMachine physical.pointer call.returnId call.returnOffset 1 ∧
      updated.byteSize = physical.entry.allocation.byteSize ∧ updated.len = physical.entry.allocation.len ∧
      AllocationCopy.snapshot updated = AllocationCopy.snapshot physical.entry.allocation ∧
      DuplicatePrefixTypeCacheOrigins.Origins finalMachine.user.payload.payload.user.types ∧
      Allocation.writeUninit (allocRange (Size.ofBytes (UInt64.ofNat call.returnOffset)) (Size.ofBytes 1)) (Size.ofBytes 8)
        (physical.entry.allocation.setExtra (CurrentCallEmptyEntryCompleteRelease.written output (UInt64.ofNat call.returnOffset)).tree) = .ok () updated := by
  obtain ⟨ret⟩ := return_data input
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  let base := CurrentCallEmptyTypedEntry.resultMachine effect fresh remaining span frames sourceFrame sourceBorrow localId valid
  let machine := afterArgumentsMachine effect fresh remaining span frames sourceFrame sourceBorrow localId valid
  let currentTracker := afterArgumentsTracker effect fresh
  obtain ⟨oldPhysical,idEq,pointerEq,offsetEq,treeEq⟩ := physical_after_effect effect fresh remaining span frames sourceFrame sourceBorrow localId valid ret.physical
  let physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place := {oldPhysical with}
  have physicalId : physical.id = call.returnId := idEq.trans ret.id
  have physicalPointer : physical.pointer = ret.pointer.value := pointerEq.trans ret.pointerEq
  have physicalOffset : physical.offset = UInt64.ofNat call.returnOffset := offsetEq.trans ret.offset
  have enabled : machine.borrowTracker = some currentTracker := rfl
  have room : currentTracker.global.nextPointerTag.value < 18446744073709551615 := effect_tag_room input effect
  have binding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id call.returnOffset 1 := by
    change CandidateCallBindings.WindowBinding base oldPhysical.pointer oldPhysical.id call.returnOffset 1
    rw [idEq,ret.id,pointerEq,ret.pointerEq]
    exact binding_after_effect effect fresh remaining span frames sourceFrame sourceBorrow localId valid ret.pointer.value call.returnId call.returnOffset 1 ret.binding
  have ghost : machine.user.payload.ghost = false := (CurrentCallEmptyEntryArguments.result_settings effect fresh remaining span frames sourceFrame sourceBorrow
    localId valid input.machine.settings.ghostOff).1
  have race : machine.dataRace = none := (CurrentCallEmptyTypedEntry.resultMachine_data effect fresh remaining span frames sourceFrame sourceBorrow localId valid).2.2.1.trans input.machine.settings.noDataRace
  have backend : machine.user.payload.payload.user.backend = .none := by
    have same : base.user.payload.payload.user.backend = before.user.payload.payload.user.backend := by cases effect <;> rfl
    exact same.trans input.machine.settings.noBackend
  have readyBefore : CurrentCallBoolProtection.WindowReady before ret.physical.id ret.physical.offset.toNat 1 := by
    rw [ret.id,ret.offsetNat]
    exact readiness.bool
  have ready : CurrentCallBoolProtection.WindowReady machine physical.id physical.offset.toNat 1 := by
    change CurrentCallBoolProtection.WindowReady base oldPhysical.id oldPhysical.offset.toNat 1
    rw [idEq,offsetEq]
    exact window_ready_after_effect effect fresh remaining span frames sourceFrame sourceBorrow localId valid ret.physical.id ret.physical.entry
      ret.physical.live ret.physical.offset.toNat 1 readyBefore
  have actualRoot : Nonempty (RootOperation physical.entry.allocation.extra currentTracker.global (rootSource effect) physical.id
      physical.pointer.provenance (UInt64.ofNat call.returnOffset) effect.allocation tracker.global.nextPointerTag room) := by
    change Nonempty (RootOperation oldPhysical.entry.allocation.extra
      (CurrentCallEmptyEntryArguments.nextTracker effect fresh).global (rootSource effect) oldPhysical.id oldPhysical.pointer.provenance
      (UInt64.ofNat call.returnOffset) effect.allocation tracker.global.nextPointerTag room)
    rw [treeEq,idEq,pointerEq,ret.pointerEq]
    exact rootOperation_after_effect input ret effect sourceFrame localId valid
  obtain ⟨certificate⟩ := actualRoot
  let output := certificate.output
  have actualOperation := certificate.actual
  have readDone := certificate.readCompleted
  have childDone := certificate.childCompleted
  have writeDone := certificate.writeCompleted
  have writtenRuntime := certificate.writeRuntime
  obtain ⟨updated,protect,extra,byteSize,length,snapshot,readyAfter,mutation⟩ := protect_from_operation options limits (remaining+1) span ctx machine currentTracker frames frame (rootSource effect)
    enabled frameBorrow place physical call.returnOffset physicalOffset binding room ghost race backend ready output actualOperation readDone childDone writeDone
  let retagged := ReturnProtection.borrowedState frames frame (rootSource effect) machine currentTracker room physical.id physical.entry output.child.tree
  let finalMachine : Before := {retagged.machine with memory := {retagged.machine.memory with live :=
    ((retagged.machine.memory.live.filter fun row => row.1 != physical.id).push (physical.id,{physical.entry with allocation := updated}))}}
  have finalBinding : CandidateCallBindings.WindowBinding finalMachine physical.pointer call.returnId call.returnOffset 1 := by
    have original : CandidateCallBindings.WindowBinding machine physical.pointer call.returnId call.returnOffset 1 := by rw [←physicalId];exact binding
    apply CurrentCallBoolWindow.replace_binding machine finalMachine physical.pointer call.returnId call.returnOffset 1 original physical.id physical.entry
      {physical.entry with allocation := updated} physical.live length byteSize rfl
    exact congrArg (fun memory => memory.live) (MemoryCopyBridge.live_update_twice machine.memory physical.id
      {physical.entry with allocation := physical.entry.allocation.setExtra output.child.tree} {physical.entry with allocation := updated})
  have finalReady : CurrentCallBoolProtection.ProfileMemoryReadiness finalMachine call := by
    refine ⟨?_,?_⟩
    · intro positive
      have length := input.actual.length
      change call.length = 0 at length
      omega
    · have offsetNat : physical.offset.toNat = call.returnOffset := by rw [physicalOffset];exact (ret.offset ▸ ret.offsetNat)
      have finalWindow : CurrentCallBoolProtection.WindowReady finalMachine physical.id physical.offset.toNat 1 := readyAfter
      rw [physicalId,offsetNat] at finalWindow
      exact finalWindow
  have origins : DuplicatePrefixTypeCacheOrigins.Origins finalMachine.user.payload.payload.user.types := by
    have same : finalMachine.user.payload.payload.user.types = before.user.payload.payload.user.types :=
      (CurrentCallEmptyTypedEntry.resultMachine_data effect fresh remaining span frames sourceFrame sourceBorrow localId valid).2.1
    rw [same]
    exact input.machine.cacheOrigins
  refine ⟨physical,room,output,certificate,rfl,updated,physicalId,physicalOffset,by rw [physicalOffset];exact ret.offset ▸ ret.offsetNat,protect,extra,?_,finalReady,finalBinding,byteSize,length,snapshot,origins,mutation⟩
  rw [extra]
  exact writtenRuntime


/-- Actual Bool return protection for every finite empty argument effect from
ORIGINAL Proposed. Frame equations are internal entry-composition data. -/
theorem protect_after_arguments {options limits remaining span before tracker argument place call data}
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (readiness : CurrentCallBoolProtection.ProfileMemoryReadiness before call)
    (effect : CurrentCallEmptyTypedEntry.Effect options before tracker argument)
    (ctx : ActualRetagContext.Context options (remaining+1) span)
    (frames : Array CompilerFrameContext.ActualFrame) (sourceFrame : CompilerFrameContext.ActualFrame) (sourceBorrow : FrameState)
    (localId : MIR.LocalId) (valid : localId < sourceFrame.locals.size)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame) :
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    let machine := afterArgumentsMachine effect fresh remaining span frames sourceFrame sourceBorrow localId valid
    let currentTracker := afterArgumentsTracker effect fresh
    ∃ physical : CandidateCurrentBoolUninitWrite.PhysicalWindow machine place,
    ∃ room : currentTracker.global.nextPointerTag.value < 18446744073709551615,
    ∃ output : GeneralBorrowForestFnEntry.Output,∃ updated : Allocation Provenance BorrowTree,
      physical.id = call.returnId ∧ physical.offset = UInt64.ofNat call.returnOffset ∧
      let retagged := ReturnProtection.borrowedState frames frame borrowFrame machine currentTracker room physical.id physical.entry output.child.tree
      let finalMachine : Before := {retagged.machine with memory := {retagged.machine.memory with live :=
        ((retagged.machine.memory.live.filter fun row => row.1 != physical.id).push (physical.id,{physical.entry with allocation := updated}))}}
      (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place (Storage.withCurrent frames frame machine) =
        .ok () (Storage.withCurrent frames (registeredFrame frame borrowFrame physical.id currentTracker.global.nextPointerTag) finalMachine) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts updated.extra output.global ∧
      CurrentCallBoolProtection.ProfileMemoryReadiness finalMachine call ∧
      CandidateCallBindings.WindowBinding finalMachine physical.pointer call.returnId call.returnOffset 1 ∧
      updated.byteSize = physical.entry.allocation.byteSize ∧ updated.len = physical.entry.allocation.len ∧
      AllocationCopy.snapshot updated = AllocationCopy.snapshot physical.entry.allocation ∧
      DuplicatePrefixTypeCacheOrigins.Origins finalMachine.user.payload.payload.user.types := by
  obtain ⟨ret⟩ := return_data input
  obtain ⟨physical,room,output,updated,idEq,_,offsetEq,protect,runtime,ready,binding,bytes,length,snapshot,origins⟩ :=
    protect_after_effect input ret readiness effect ctx frames sourceFrame sourceBorrow localId valid frame borrowFrame frameBorrow
  exact ⟨physical,room,output,updated,idEq,offsetEq,protect,runtime,ready,binding,bytes,length,snapshot,origins⟩

open Lean Elab Command in
run_cmd do
  for declaration in #[``write_queries_locations,``zero_sifa_write_queries,``extended_parent_live,``complete_bool_holdings,``complete_constructor_reserved,``wildcard_constructor_reserved,``complete_prepared_read,``mutable_constructor_reserved,``mutable_constructor_permission,``protect_root_after_arguments,``rootOperation_after_effect,``root_complete_after_effect,``boolTree_other,``rootOperation_complete,``effect_source_leaf,``rootOperation_of_zero,``rootOperation_of_complete,``zero_sifa_write_callback,``boolAfter_rights_of_parent_authority,``zero_sifa_child_write_unique,``boolAfter_rights_of_authority,``source_access_locations,``mutable_constructor_shape,``zero_fnentry_write_retained,``zero_sifa_write_range_retained,``zero_sifa_child_write_retained,``boolChild_physical,``boolAfter_query,``boolChild_ancestry,``boolAfter_cases,``boolAfter_zero_node,``boolAfter_authority,``boolAfter_old_path_back,``boolChild_path_iff,``zero_sifa_write_retained_callback,``protect_after_arguments,``return_data,``protect_after_effect,``operation_after_effect,``effect_tag_room,``zero_slot_order,``zero_slot_distinct,``complete_fnentry_write,``protect_from_operation,``original_owned_after_effect,``zero_root_owned,``zero_fnentry_write,``window_ready_after_effect,``bool_constructor_representation,``bool_attached_size,``boolAfter_old_node,``boolAfter_child_node,``original_runtime_after_effect,``zero_write_authorization,``zero_rights_child_owned,``zero_rights_owned_shape,``zero_rights_materialized,``zero_fnentry,``zero_associated_read,``zero_parent_normal_owned,``zero_normal_of_foreign,``binding_after_effect,``physical_after_effect,``effect_bool_live,``effect_addresses,``zero_completes_of_exposed_return,``zero_concrete_range] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved empty Bool dependency {dependency}"

end
end DuplicatePrefix.CurrentCallEmptyEntryBool
