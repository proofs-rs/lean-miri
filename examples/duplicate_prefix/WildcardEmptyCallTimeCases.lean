import duplicate_prefix.DuplicatePrefixEmptyReferenceInput
import duplicate_prefix.WildcardOrderedMissAddress
import duplicate_prefix.WildcardUnexposedInteriorAddress
import duplicate_prefix.WildcardGeneralHitReborrow
namespace DuplicatePrefix.WildcardEmptyCallTimeCases
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixEmptyReferenceInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/-- Only the immediate predecessor is outside. The source does not inspect
other older intervals; no successful lookup or address history is a premise. -/
def ImmediateGap {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64) : Prop :=
  ∃ position row info,
    WildcardInteriorHitAddress.Cut addresses.intToPtrMap address (position+1) ∧
    addresses.intToPtrMap[position]? = some row ∧ memory.getAllocInfo row.allocId = .ok info ∧
    ¬address-row.address < info.size.bytes

/-- Exhaustive raw cases for the existing wildcard candidate. This is a
coverage lemma for geometry/metadata, NOT a whole-call safety theorem. -/
def Cases {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64) : Prop :=
  WildcardOrderedMissAddress.Miss addresses address ∨
  WildcardUnexposedInteriorAddress.Geometry addresses address (fun id => (memory.getAllocInfo id).toOption.map (·.size)) ∨
  (∃ id base info, memory.getAllocInfo id = .ok info ∧ addresses.exposed.contains id = true ∧
    addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ ∧
    TargetMetadata context memory addresses id none ∧
    WildcardGeneralHitReborrow.Geometry addresses.intToPtrMap address base id info.size) ∨
  ImmediateGap memory addresses address

theorem classify {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64) (input : Wildcard context memory addresses) :
    Cases context memory addresses address := by
  rcases WildcardEmptyCoherentResolution.classify memory addresses address input.coherent input.nonstrict input.sizes with
    ⟨position,row,valid,present,same,done⟩ | ⟨cut,partition,rest⟩
  · have member := Array.mem_of_getElem? present
    cases exposed : addresses.exposed.contains row.allocId with
    | false =>
      apply Or.inl
      apply Or.inr
      refine ⟨row.allocId,position,valid,input.coherent.ordered,?_,exposed⟩
      cases row with
      | mk base id => dsimp only at same;subst base;exact present
    | true =>
      have target := input.targets row member exposed
      obtain ⟨info,known⟩ := target_metadata_known context memory addresses row.allocId none target
      refine Or.inr (Or.inr (Or.inl ⟨row.allocId,row.address,info,known,exposed,input.cached row member exposed,target,?_⟩))
      exact Or.inl ⟨same.symm,position,valid,input.coherent.ordered,by cases row;exact present⟩
  · rcases rest with ⟨zero,done⟩ | ⟨row,info,nonzero,present,known,nondead,done⟩
    · apply Or.inl
      apply Or.inl
      intro row member
      obtain ⟨index,valid,equal⟩ := Array.mem_iff_getElem.mp member
      rw [←equal]
      exact partition.2.2 index valid (by omega)
    · have position : cut-1+1=cut := by omega
      have partition' : WildcardInteriorHitAddress.Cut addresses.intToPtrMap address (cut-1+1) := by simpa only [position] using partition
      have member := Array.mem_of_getElem? present
      cases exposed : addresses.exposed.contains row.allocId with
      | false =>
        refine Or.inr (Or.inl ⟨cut-1,row,info.size,partition',present,?_,exposed⟩)
        simp only [known,Except.toOption,Option.map_some]
      | true =>
        by_cases inside : address-row.address < info.size.bytes
        · refine Or.inr (Or.inr (Or.inl ⟨row.allocId,row.address,info,known,exposed,input.cached row member exposed,input.targets row member exposed,?_⟩))
          exact Or.inr ⟨cut-1,partition',by cases row;exact present,inside⟩
        · exact Or.inr (Or.inr (Or.inr ⟨cut-1,row,info,partition',present,known,inside⟩))

/-- The local predecessor gap gives the real source miss, even when an older
interval overlaps the address. No global Apart/all-predecessors condition. -/
theorem immediate_allocation {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64)
    (nonstrict : addresses.provenanceMode ≠ .strict) (gap : ImmediateGap memory addresses address) :
    addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup memory) = .ok none := by
  obtain ⟨position,row,info,partition,present,known,outside⟩ := gap
  have search := WildcardInteriorHitAddress.inverse_cut addresses.intToPtrMap address (position+1) partition
  have size : (GlobalAddressLiveErrorExclusion.lookup memory).sizeOf row.allocId = some info.size := by
    simp only [GlobalAddressLiveErrorExclusion.lookup,known,Except.toOption,Option.map_some]
  unfold GlobalAddressState.allocIdFromAddr
  unfold_global_data ".GlobalAddressState.inverseSearch"
  simp [nonstrict,search,present,size,outside,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
/-- The real typed resolver returns unresolved for the immediate-predecessor
miss. Width, operation success and a complete address history are unnecessary. -/
theorem immediate_resolve {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (state : ValidityMachine.State K U) (address : UInt64)
    (nonstrict : state.machine.user.addresses.provenanceMode ≠ .strict)
    (gap : ImmediateGap state.machine.memory state.machine.user.addresses address) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) state = .ok none state := by
  have allocated := immediate_allocation state.machine.memory state.machine.user.addresses address nonstrict gap
  have pointer : state.machine.user.addresses.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0
      (GlobalAddressLiveErrorExclusion.lookup state.machine.memory) pointers.arithmetic = .ok none := by
    simp only [GlobalAddressState.ptrGetAlloc,Pointer.new,Size.ofBytes,allocated,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  simp only [Pointer.new,GlobalAddressLiveErrorExclusion.lookup] at pointer
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,
    pointer,get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]

/-- Every wildcard empty input in the stated candidate has one raw case.
No case/family membership is supplied by the caller. -/
theorem from_candidate {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64)
    (input : Candidate context memory addresses (Pointer.new (some .wildcard) (Size.ofBytes address))) :
    Cases context memory addresses address := classify context memory addresses address input.2

end DuplicatePrefix.WildcardEmptyCallTimeCases
