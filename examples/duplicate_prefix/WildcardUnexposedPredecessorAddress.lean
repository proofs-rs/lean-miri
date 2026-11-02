import duplicate_prefix.WildcardEmptyFamilyFormation
namespace DuplicatePrefix.WildcardUnexposedPredecessorAddress
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Raw source predecessor geometry and actual size supplier. Exposure rejects
this candidate whether the queried address is inside its range or beyond it;
size lookup still occurs before that rejection and is therefore not omitted. -/
def Geometry {K : Type} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState) (address : UInt64) : Prop :=
  ∃ position row size,WildcardInteriorHitAddress.Cut addresses.intToPtrMap address (position+1) ∧
    addresses.intToPtrMap[position]?=some row ∧ WildcardMetadataGap.SizeRow memory row.allocId size ∧
    addresses.exposed.contains row.allocId=false

/-- Actual source binary search, real size callback, then exposure rejection.
This covers the previously separate unexposed interior branch. No lookup
success, allocation liveness callback, or chosen resolver result is assumed. -/
theorem allocation_miss {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState) (address : UInt64)
    (mode : addresses.provenanceMode≠.strict) (geometry : Geometry memory addresses address) :
    addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup memory)=.ok none := by
  obtain ⟨position,row,size,partition,present,metadata,unexposed⟩:=geometry
  have search:=WildcardInteriorHitAddress.inverse_cut addresses.intToPtrMap address (position+1) partition
  have missing : row.allocId∉addresses.exposed := by simpa using unexposed
  have sizeKnown:=WildcardMetadataGap.size_of_row memory row.allocId size metadata
  unfold GlobalAddressState.allocIdFromAddr
  unfold_global_data ".GlobalAddressState.inverseSearch"
  by_cases inside : address-row.address<size.bytes
  all_goals simp [mode,search,present,GlobalAddressLiveErrorExclusion.lookup,sizeKnown,missing,inside,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

theorem pointer_miss {K} (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState) (address : UInt64)
    (arithmetic : PointerArithmetic) (mode : addresses.provenanceMode≠.strict) (geometry : Geometry memory addresses address) :
    addresses.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0 (GlobalAddressLiveErrorExclusion.lookup memory) arithmetic=.ok none := by
  simp only [GlobalAddressState.ptrGetAlloc,Pointer.new,Size.ofBytes,allocation_miss memory addresses address mode geometry,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

/-- The actual typed resolver also preserves its machine state on this source
miss. Its zero-size check still performs the size/exposure resolution. -/
theorem resolve_miss {K U : Type} (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address : UInt64)
    (mode : before.machine.user.addresses.provenanceMode≠.strict)
    (geometry : Geometry before.machine.memory before.machine.user.addresses address) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before=.ok none before := by
  have resolution:=pointer_miss before.machine.memory before.machine.user.addresses address pointers.arithmetic mode geometry
  simp only [GlobalAddressLiveErrorExclusion.lookup,Pointer.new] at resolution
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,resolution,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]
end DuplicatePrefix.WildcardUnexposedPredecessorAddress
