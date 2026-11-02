import duplicate_prefix.WildcardUnexposedInteriorAddress
namespace DuplicatePrefix.WildcardImmediateGapAddress
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- The actual source selects only the immediate predecessor. Older overlapping
intervals impose no extra gap condition. All fields describe initial data. -/
def Geometry (entries : Array InverseAddressEntry) (address : UInt64)
    (sizeOf : AllocId → Option Size) : Prop :=
  ∃ position row size, WildcardInteriorHitAddress.Cut entries address (position+1) ∧
    entries[position]? = some row ∧ sizeOf row.allocId = some size ∧
    ¬address-row.address < size.bytes

/-- Raw initial metadata suppliers with their source-computed size. In
particular function/vaList/vtable/typeId predecessors have zero size. -/
def globalSize (descriptor : GlobalAllocation) : Size :=
  match descriptor.kind with | .memory | .static => descriptor.size | _ => Size.ZERO

inductive SizeData {K : Type} (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (id : AllocId) : Size → Prop where
  | live (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
      (present : memory.live.find? (fun row => row.1 == id) = some (id,entry)) : SizeData memory id entry.allocation.byteSize
  | functionRow (absent : memory.live.find? (fun row => row.1 == id) = none)
      (present : memory.hasFunctionPointer id = true) : SizeData memory id Size.ZERO
  | vaListRow (absent : memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : memory.hasFunctionPointer id = false) (present : memory.hasVaListId id = true) : SizeData memory id Size.ZERO
  | globalRow (descriptor : GlobalAllocation) (absent : memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : memory.hasFunctionPointer id = false) (noVaList : memory.hasVaListId id = false)
      (present : memory.findGlobal? id = some descriptor) : SizeData memory id (globalSize descriptor)
  | dead (entry : DeadAllocation) (absent : memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : memory.hasFunctionPointer id = false) (noVaList : memory.hasVaListId id = false)
      (noGlobal : memory.findGlobal? id = none)
      (present : memory.dead.find? (fun row => row.allocId == id) = some entry) : SizeData memory id entry.size

theorem size_of_data {K : Type} (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (id : AllocId) (size : Size) (data : SizeData memory id size) :
    (memory.getAllocInfo id).toOption.map (·.size) = some size := by
  cases data with
  | live entry present => exact WildcardGapAddress.size_of_live memory id entry present
  | functionRow absent present => simp only [MemoryState.getAllocInfo,absent,present,↓reduceIte];rfl
  | vaListRow absent noFunction present =>
    unfold MemoryState.hasVaListId at present
    simp only [MemoryState.getAllocInfo,absent,noFunction,present,Bool.false_eq_true,↓reduceIte];rfl
  | globalRow descriptor absent noFunction noVaList present =>
    unfold MemoryState.hasVaListId at noVaList
    simp only [MemoryState.getAllocInfo,absent,noFunction,noVaList,present,Bool.false_eq_true,↓reduceIte]
    unfold globalSize
    cases descriptor.kind <;> rfl
  | dead entry absent noFunction noVaList noGlobal present =>
    unfold MemoryState.hasVaListId at noVaList
    simp only [MemoryState.getAllocInfo,absent,noFunction,noVaList,noGlobal,present,Bool.false_eq_true,↓reduceIte];rfl

def RawGeometry {K : Type} (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (state : GlobalAddressState) (address : UInt64) : Prop :=
  ∃ position row size, WildcardInteriorHitAddress.Cut state.intToPtrMap address (position+1) ∧
    state.intToPtrMap[position]? = some row ∧ SizeData memory row.allocId size ∧ ¬address-row.address < size.bytes

theorem geometry_of_raw {K : Type} (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (state : GlobalAddressState) (address : UInt64) (raw : RawGeometry memory state address) :
    Geometry state.intToPtrMap address (fun id => (memory.getAllocInfo id).toOption.map (·.size)) := by
  obtain ⟨position,row,size,partition,present,data,outside⟩ := raw
  exact ⟨position,row,size,partition,present,size_of_data memory row.allocId size data,outside⟩

theorem allocation (state : GlobalAddressState) (address : UInt64) (hooks : AddressLookupHooks)
    (nonstrict : state.provenanceMode ≠ .strict) (geometry : Geometry state.intToPtrMap address hooks.sizeOf) :
    state.allocIdFromAddr address 0 hooks = .ok none := by
  obtain ⟨position,row,size,partition,present,known,outside⟩ := geometry
  have search := WildcardInteriorHitAddress.inverse_cut state.intToPtrMap address (position+1) partition
  unfold GlobalAddressState.allocIdFromAddr
  unfold_global_data ".GlobalAddressState.inverseSearch"
  simp [nonstrict,search,present,known,outside,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

theorem resolve {K U : Type} (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address : UInt64)
    (nonstrict : before.machine.user.addresses.provenanceMode ≠ .strict)
    (geometry : Geometry before.machine.user.addresses.intToPtrMap address
      (fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size))) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before = .ok none before := by
  have allocated := allocation before.machine.user.addresses address
    (⟨fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size),fun id => some (before.machine.memory.isAllocLive id)⟩ : AddressLookupHooks) nonstrict geometry
  have pointer : before.machine.user.addresses.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0
      (⟨fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size),fun id => some (before.machine.memory.isAllocLive id)⟩ : AddressLookupHooks)
      pointers.arithmetic = .ok none := by
    simp only [GlobalAddressState.ptrGetAlloc,Pointer.new,Size.ofBytes,allocated,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  simp only [Pointer.new] at pointer
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,pointer,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]
end DuplicatePrefix.WildcardImmediateGapAddress
