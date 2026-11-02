import duplicate_prefix.CurrentCallConversionChoiceProtocol
import duplicate_prefix.CurrentCallConversionInfoRows
import duplicate_prefix.CurrentCallConversionAddressFrames
import duplicate_prefix.GlobalAddressRangeFormation
import duplicate_prefix.WildcardGeneralHitReborrow

namespace DuplicatePrefix.CurrentCallConversionBoolQueryFrame
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open WildcardInteriorHitAddress WildcardEmptyFamilyFormation GlobalAddressRangeFormation
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

open Lean Elab Term in
elab "bool_query_rule" suffix:str : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_)=>
    if name.toString.endsWith suffix.getString then some name else none
  match names with
  | [name]=>return mkConst name
  | _=>throwError "expected one checked address helper ending {suffix.getString}"

/-- Inserting one row preserves each old row at its exact shifted position;
allocation IDs need not be unique in the inverse vector. -/
theorem row_insert (entries : Array InverseAddressEntry) (position : Nat) (valid : position<entries.size)
    (row : InverseAddressEntry) (present : entries[position]?=some row)
    (inserted : InverseAddressEntry) (cut : Nat) (bounded : cut≤entries.size) :
    ∃next,next<(entries.insertIdx cut inserted bounded).size ∧
      (entries.insertIdx cut inserted bounded)[next]?=some row := by
  have actual : entries[position]=row:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans present)
  by_cases before : position<cut
  · have nextValid : position<(entries.insertIdx cut inserted bounded).size:=by rw [Array.size_insertIdx];omega
    refine ⟨position,nextValid,?_⟩
    rw [Array.getElem?_eq_getElem nextValid,Array.getElem_insertIdx bounded nextValid]
    simp only [before,↓reduceDIte,actual]
  · have nextValid : position+1<(entries.insertIdx cut inserted bounded).size:=by rw [Array.size_insertIdx];omega
    refine ⟨position+1,nextValid,?_⟩
    rw [Array.getElem?_eq_getElem nextValid,Array.getElem_insertIdx bounded nextValid]
    simp only [show ¬position+1<cut by omega,show position+1≠cut by omega,↓reduceDIte,Nat.add_sub_cancel,actual]

/-- Existing exact/interior Bool hit geometry survives the real insertion.
Numeric placement prevents a newly inserted row from stealing an interior hit. -/
theorem geometry_insert (entries : Array InverseAddressEntry) (sizes : AllocId→Size)
    (ordered : Ordered entries) (apart : Apart entries sizes)
    (address base : UInt64) (id : AllocId) (size : Size)
    (geometry : WildcardGeneralHitReborrow.Geometry entries address base id size)
    (sizeEq : sizes id=size) (inserted : AllocId) (newBase : UInt64) (cut : Nat)
    (partition : Cut entries newBase cut) (placement : Placement entries sizes inserted newBase cut) :
    WildcardGeneralHitReborrow.Geometry (entries.insertIdx cut ⟨newBase,inserted⟩ partition.1) address base id size := by
  have nextOrdered:Ordered (entries.insertIdx cut ⟨newBase,inserted⟩ partition.1):=
    (bool_query_rule ".GlobalAddressExposureFormation.insert_ordered") entries inserted newBase cut partition ordered
  have nextApart:=GlobalAddressRangeFormation.insert entries sizes apart inserted newBase cut partition.1 placement
  rcases geometry with ⟨equal,position,valid,_,present⟩ | ⟨position,oldCut,present,inside⟩
  · obtain ⟨next,nextValid,nextPresent⟩:=row_insert entries position valid ⟨base,id⟩ present ⟨newBase,inserted⟩ cut partition.1
    exact Or.inl ⟨equal,next,nextValid,nextOrdered,nextPresent⟩
  · have valid : position<entries.size:=by have bounded:=oldCut.1;omega
    have actual : entries[position]=⟨base,id⟩:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans present)
    have afterBase : base<address:=by
      have before:=oldCut.2.1 position valid (Nat.lt_succ_self _)
      rw [actual] at before
      exact before
    have lower : base≤address:=UInt64.le_of_lt afterBase
    have insideNat : address.toNat<base.toNat+size.bytes.toNat:=by
      have raw:=UInt64.lt_iff_toNat_lt.mp inside
      rw [UInt64.toNat_sub_of_le _ _ lower] at raw
      omega
    obtain ⟨next,nextValid,nextPresent⟩:=row_insert entries position valid ⟨base,id⟩ present ⟨newBase,inserted⟩ cut partition.1
    have nextActual : (entries.insertIdx cut ⟨newBase,inserted⟩ partition.1)[next]=⟨base,id⟩:=
      Option.some.inj ((Array.getElem?_eq_getElem nextValid).symm.trans nextPresent)
    have beforeNext : ∀valid : next+1<(entries.insertIdx cut ⟨newBase,inserted⟩ partition.1).size,
        address<(entries.insertIdx cut ⟨newBase,inserted⟩ partition.1)[next+1].address:=by
      intro bounded
      have separation:=nextApart next (next+1) bounded (Nat.lt_succ_self _)
      rw [nextActual,sizeEq] at separation
      apply UInt64.lt_iff_toNat_lt.mpr
      exact Nat.lt_of_lt_of_le insideNat separation
    exact Or.inr ⟨next,cut_of_ordered _ address base id next nextValid nextOrdered nextPresent afterBase beforeNext,nextPresent,inside⟩

/-- A real metadata query fixes the canonical size used by the weak converter
invariant; no fixed-catalog identity or inverse-ID uniqueness is required. -/
theorem size_of_info {K : Type} {memory : MemoryState Provenance BorrowTree K} {id : AllocId}
    {info : AllocationInfo} {size : Size} (queried : memory.getAllocInfo id=.ok info) (equal : info.size=size) :
    CurrentCallConversionInfoRows.sizes memory id=size:=
  (CurrentCallConversionInfoRows.queried_size queried).trans equal


/-- Cache formation never changes provenance mode or exposure, on either
success or an error prefix. -/
theorem cache_fields (state : GlobalAddressState) (id : AllocId) (address : UInt64) :
    (state.cacheAddress id address).state.provenanceMode=state.provenanceMode ∧
    (state.cacheAddress id address).state.exposed=state.exposed := by
  unfold GlobalAddressState.cacheAddress
  unfold_internal ".GlobalAddressState.findBase"
  simp only [Id.run,pure]
  split
  · exact ⟨rfl,rfl⟩
  · split
    · exact ⟨rfl,rfl⟩
    · split
      · split <;> exact ⟨rfl,rfl⟩
      · split <;> exact ⟨rfl,rfl⟩

/-- The actual nonzero cache operation installs precisely the vector row
identified by its raw cut. Operation success is a conclusion. -/
theorem cache_inverse (state : GlobalAddressState) (id : AllocId) (address : UInt64)
    (uncached : state.baseAddr.find? (fun row=>row.allocId==id)=none) (nonzero : address≠0)
    (cut : Nat) (partition : Cut state.intToPtrMap address cut) :
    (state.cacheAddress id address).outcome=.ok () ∧
    (state.cacheAddress id address).state.intToPtrMap=state.intToPtrMap.insertIdx cut ⟨address,id⟩ partition.1 := by
  have search:=WildcardInteriorHitAddress.inverse_cut state.intToPtrMap address cut partition
  have nonzeroBool : (address==0)=false:=by simpa using nonzero
  unfold GlobalAddressState.cacheAddress
  unfold_internal ".GlobalAddressState.findBase"
  simp only [uncached,Option.map_none,search,nonzeroBool,Bool.false_eq_true,↓reduceIte,partition.1,↓reduceDIte]
  exact ⟨rfl,rfl⟩

/-- A typeId zero address adds no inverse row and preserves initial hit
geometry without a placement or inverse allocation-ID freshness condition. -/
theorem cache_zero (state : GlobalAddressState) (id : AllocId)
    (uncached : state.baseAddr.find? (fun row=>row.allocId==id)=none) :
    (state.cacheAddress id 0).outcome=.ok () ∧(state.cacheAddress id 0).state.intToPtrMap=state.intToPtrMap := by
  unfold GlobalAddressState.cacheAddress
  unfold_internal ".GlobalAddressState.findBase"
  simp only [uncached,Option.map_none,BEq.rfl,↓reduceIte]
  exact ⟨rfl,rfl⟩

/-- One real cache insertion preserves the already represented Bool hit,
including holes below and rows above its base. -/
theorem cache_geometry (state : GlobalAddressState) (sizes : AllocId→Size)
    (ordered : Ordered state.intToPtrMap) (apart : Apart state.intToPtrMap sizes)
    (address base : UInt64) (id : AllocId) (size : Size)
    (geometry : WildcardGeneralHitReborrow.Geometry state.intToPtrMap address base id size)
    (sizeEq : sizes id=size) (inserted : AllocId) (newBase : UInt64)
    (uncached : state.baseAddr.find? (fun row=>row.allocId==inserted)=none) (nonzero : newBase≠0)
    (cut : Nat) (partition : Cut state.intToPtrMap newBase cut) (placement : Placement state.intToPtrMap sizes inserted newBase cut) :
    (state.cacheAddress inserted newBase).outcome=.ok () ∧
    WildcardGeneralHitReborrow.Geometry (state.cacheAddress inserted newBase).state.intToPtrMap address base id size := by
  obtain ⟨done,inverse⟩:=cache_inverse state inserted newBase uncached nonzero cut partition
  refine ⟨done,?_⟩
  rw [inverse]
  exact geometry_insert state.intToPtrMap sizes ordered apart address base id size geometry sizeEq inserted newBase cut partition placement

/-- Positive scalar size one and zero use the same wildcard search address. -/
theorem allocation_one_zero (state : GlobalAddressState) (address : UInt64) (hooks : AddressLookupHooks) :
    state.allocIdFromAddr address 1 hooks=state.allocIdFromAddr address 0 hooks := by rfl

theorem allocation_geometry (state : GlobalAddressState) (address base : UInt64) (id : AllocId) (size : Size)
    (geometry : WildcardGeneralHitReborrow.Geometry state.intToPtrMap address base id size)
    (hooks : AddressLookupHooks) (mode : state.provenanceMode≠.strict) (known : hooks.sizeOf id=some size)
    (exposed : state.exposed.contains id=true) (live : hooks.isLive id=some true) :
    state.allocIdFromAddr address 0 hooks=.ok (some id) ∧state.allocIdFromAddr address 1 hooks=.ok (some id) := by
  have zero : state.allocIdFromAddr address 0 hooks=.ok (some id):=by
    rcases geometry with ⟨same,position,valid,ordered,row⟩ | ⟨position,cut,row,inside⟩
    · subst address
      exact WildcardOrderedHitAddress.allocation state base id hooks position valid ordered row mode exposed live
    · exact WildcardInteriorHitAddress.allocation state address base id hooks size position mode cut row known inside exposed live
  exact ⟨zero,(allocation_one_zero state address hooks).trans zero⟩

/-- Both real scalar queries retain the same allocation and relative offset;
this includes non-base Bool pointers in the original return place. -/
theorem pointer_geometry (state : GlobalAddressState) (address base : UInt64) (id : AllocId) (size : Size)
    (geometry : WildcardGeneralHitReborrow.Geometry state.intToPtrMap address base id size)
    (hooks : AddressLookupHooks) (arithmetic : PointerArithmetic) (width : arithmetic=⟨Size.ofBytes 8⟩)
    (mode : state.provenanceMode≠.strict) (known : hooks.sizeOf id=some size)
    (exposed : state.exposed.contains id=true) (live : hooks.isLive id=some true)
    (cached : state.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩) :
    state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0 hooks arithmetic=.ok (some (id,Size.ofBytes (address-base))) ∧
    state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 1 hooks arithmetic=.ok (some (id,Size.ofBytes (address-base))) := by
  have zero : state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0 hooks arithmetic=.ok (some (id,Size.ofBytes (address-base))):=by
    rcases geometry with ⟨same,position,valid,ordered,row⟩ | ⟨position,cut,row,inside⟩
    · subst address
      simpa only [UInt64.sub_self,Size.ZERO,Size.ofBytes] using
        WildcardOrderedHitAddress.pointer state base id hooks position valid ordered row arithmetic width mode exposed live cached
    · exact WildcardInteriorHitAddress.pointer state address base id hooks size position arithmetic width mode cut row known inside exposed live cached
  refine ⟨zero,?_⟩
  unfold GlobalAddressState.ptrGetAlloc
  simp only [Pointer.new,Size.ofBytes]
  rw [allocation_one_zero]
  exact zero


/-- Actual nonzero cache formation preserves both real Bool wildcard queries.
Only the chosen Bool metadata hooks are read; unrelated inverse IDs may repeat. -/
theorem cache_pointer (state : GlobalAddressState) (sizes : AllocId→Size)
    (ordered : Ordered state.intToPtrMap) (apart : Apart state.intToPtrMap sizes)
    (address base : UInt64) (id : AllocId) (size : Size)
    (geometry : WildcardGeneralHitReborrow.Geometry state.intToPtrMap address base id size)
    (sizeEq : sizes id=size) (inserted : AllocId) (newBase : UInt64)
    (uncached : state.baseAddr.find? (fun row=>row.allocId==inserted)=none) (nonzero : newBase≠0)
    (cut : Nat) (partition : Cut state.intToPtrMap newBase cut) (placement : Placement state.intToPtrMap sizes inserted newBase cut)
    (hooks : AddressLookupHooks) (arithmetic : PointerArithmetic) (width : arithmetic=⟨Size.ofBytes 8⟩)
    (mode : state.provenanceMode≠.strict) (known : hooks.sizeOf id=some size)
    (exposed : state.exposed.contains id=true) (live : hooks.isLive id=some true)
    (cached : state.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩) :
    (state.cacheAddress inserted newBase).outcome=.ok () ∧
    (state.cacheAddress inserted newBase).state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0 hooks arithmetic=
      .ok (some (id,Size.ofBytes (address-base))) ∧
    (state.cacheAddress inserted newBase).state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 1 hooks arithmetic=
      .ok (some (id,Size.ofBytes (address-base))) := by
  obtain ⟨done,geometryAfter⟩:=cache_geometry state sizes ordered apart address base id size geometry sizeEq inserted newBase uncached nonzero cut partition placement
  have fields:=cache_fields state inserted newBase
  have oldBase:=CurrentCallConversionCacheFrames.base_preserved state inserted newBase id ⟨id,base⟩ cached
  have query:=pointer_geometry (state.cacheAddress inserted newBase).state address base id size geometryAfter hooks arithmetic width
    (by rw [fields.1];exact mode) known (by rw [fields.2];exact exposed) live oldBase
  exact ⟨done,query⟩

/-- The real zero-address typeId branch preserves Bool lookup without adding
an inverse row or requiring a placement certificate. -/
theorem cache_zero_pointer (state : GlobalAddressState) (inserted : AllocId)
    (uncached : state.baseAddr.find? (fun row=>row.allocId==inserted)=none)
    (address base : UInt64) (id : AllocId) (size : Size)
    (geometry : WildcardGeneralHitReborrow.Geometry state.intToPtrMap address base id size)
    (hooks : AddressLookupHooks) (arithmetic : PointerArithmetic) (width : arithmetic=⟨Size.ofBytes 8⟩)
    (mode : state.provenanceMode≠.strict) (known : hooks.sizeOf id=some size)
    (exposed : state.exposed.contains id=true) (live : hooks.isLive id=some true)
    (cached : state.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩) :
    (state.cacheAddress inserted 0).outcome=.ok () ∧
    (state.cacheAddress inserted 0).state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0 hooks arithmetic=
      .ok (some (id,Size.ofBytes (address-base))) ∧
    (state.cacheAddress inserted 0).state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 1 hooks arithmetic=
      .ok (some (id,Size.ofBytes (address-base))) := by
  obtain ⟨done,inverse⟩:=cache_zero state inserted uncached
  have geometryAfter : WildcardGeneralHitReborrow.Geometry (state.cacheAddress inserted 0).state.intToPtrMap address base id size:=by rw [inverse];exact geometry
  have fields:=cache_fields state inserted 0
  have oldBase:=CurrentCallConversionCacheFrames.base_preserved state inserted 0 id ⟨id,base⟩ cached
  have query:=pointer_geometry (state.cacheAddress inserted 0).state address base id size geometryAfter hooks arithmetic width
    (by rw [fields.1];exact mode) known (by rw [fields.2];exact exposed) live oldBase
  exact ⟨done,query⟩


private theorem present_of_member (entries : Array InverseAddressEntry) (row : InverseAddressEntry)
    (member : row∈entries) : ∃position,position<entries.size ∧entries[position]?=some row := by
  obtain ⟨position,valid,equal⟩:=Array.mem_iff_getElem.mp member
  exact ⟨position,valid,(Array.getElem?_eq_getElem valid).trans (congrArg some equal)⟩

/-- The pure data projection of a checked cache step never deletes an old
inverse row, including its zero and out-of-bounds cases. -/
theorem cacheData_rows (state : GlobalAddressState) (id : AllocId) (address : UInt64)
    (row : InverseAddressEntry) (member : row∈state.intToPtrMap) :
    row∈(CurrentCallConversionChoiceProtocol.cacheData state id address).intToPtrMap := by
  unfold CurrentCallConversionChoiceProtocol.cacheData
  split
  · exact member
  · dsimp only
    unfold Array.insertIdxIfInBounds
    split
    · exact Array.mem_insertIdx.mpr (Or.inr member)
    · exact member

private theorem geometry_rows (old next : Array InverseAddressEntry) (sizes : AllocId→Size)
    (preserved : ∀row∈old,row∈next) (ordered : Ordered next) (apart : Apart next sizes)
    (address base : UInt64) (id : AllocId) (size : Size)
    (geometry : WildcardGeneralHitReborrow.Geometry old address base id size) (sizeEq : sizes id=size) :
    WildcardGeneralHitReborrow.Geometry next address base id size := by
  rcases geometry with ⟨equal,position,valid,_,present⟩ | ⟨position,oldCut,present,inside⟩
  · have member : (⟨base,id⟩ : InverseAddressEntry)∈old:=by
      have actual:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans present)
      rw [←actual]
      exact Array.getElem_mem valid
    obtain ⟨index,indexValid,indexPresent⟩:=present_of_member next ⟨base,id⟩ (preserved _ member)
    exact Or.inl ⟨equal,index,indexValid,ordered,indexPresent⟩
  · have valid : position<old.size:=by have bound:=oldCut.1;omega
    have actual : old[position]=⟨base,id⟩:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans present)
    have member : (⟨base,id⟩ : InverseAddressEntry)∈old:=by rw [←actual];exact Array.getElem_mem valid
    have afterBase : base<address:=by
      have before:=oldCut.2.1 position valid (Nat.lt_succ_self _)
      rw [actual] at before
      exact before
    have insideNat : address.toNat<base.toNat+size.bytes.toNat:=by
      have raw:=UInt64.lt_iff_toNat_lt.mp inside
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt afterBase)] at raw
      omega
    obtain ⟨index,indexValid,indexPresent⟩:=present_of_member next ⟨base,id⟩ (preserved _ member)
    have nextActual : next[index]=⟨base,id⟩:=Option.some.inj ((Array.getElem?_eq_getElem indexValid).symm.trans indexPresent)
    have beforeNext : ∀valid : index+1<next.size,address<next[index+1].address:=by
      intro bounded
      have separation:=apart index (index+1) bounded (Nat.lt_succ_self _)
      rw [nextActual,sizeEq] at separation
      exact UInt64.lt_iff_toNat_lt.mpr (Nat.lt_of_lt_of_le insideNat separation)
    exact Or.inr ⟨index,cut_of_ordered next address base id index indexValid ordered indexPresent afterBase beforeNext,indexPresent,inside⟩

/-- Replay uses the already-derived successor allocator invariants. This
avoids exposing internal placement choices from each acquisition branch. -/
theorem cacheData_geometry (state : GlobalAddressState) (inserted : AllocId) (newBase : UInt64) (sizes : AllocId→Size)
    (ordered : Ordered (CurrentCallConversionChoiceProtocol.cacheData state inserted newBase).intToPtrMap)
    (apart : Apart (CurrentCallConversionChoiceProtocol.cacheData state inserted newBase).intToPtrMap sizes)
    (address base : UInt64) (id : AllocId) (size : Size)
    (geometry : WildcardGeneralHitReborrow.Geometry state.intToPtrMap address base id size) (sizeEq : sizes id=size) :
    WildcardGeneralHitReborrow.Geometry (CurrentCallConversionChoiceProtocol.cacheData state inserted newBase).intToPtrMap address base id size :=
  geometry_rows state.intToPtrMap _ sizes (cacheData_rows state inserted newBase) ordered apart address base id size geometry sizeEq

end DuplicatePrefix.CurrentCallConversionBoolQueryFrame
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionBoolQueryFrame" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved wildcard Bool query frame dependency {dependency}"
