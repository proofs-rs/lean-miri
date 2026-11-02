import duplicate_prefix.GlobalAddressPhysicalRowHistory
import duplicate_prefix.OrdinaryPhysicalValidity
import duplicate_prefix.WildcardGeneralHitReborrow
namespace DuplicatePrefix.OrdinaryDistinctAddressBoundary
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

private theorem geometry_row (entries : Array InverseAddressEntry) (address base : UInt64) (id : AllocId) (size : Size)
    (geometry : WildcardGeneralHitReborrow.Geometry entries address base id size) :
    ∃ index, index < entries.size ∧ entries[index]? = some ⟨base,id⟩ := by
  rcases geometry with ⟨_,index,valid,_,row⟩ | ⟨index,cut,row,_⟩
  · exact ⟨index,valid,row⟩
  · exact ⟨index,by have bound := cut.1;omega,row⟩

private theorem live_size {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (sizes : AllocId → Size)
    (state : GlobalAddressRangeResources.State memory addresses sizes)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (base : UInt64)
    (live : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (member : (⟨base,id⟩ : InverseAddressEntry) ∈ addresses.intToPtrMap) :
    sizes id = entry.allocation.byteSize := by
  have row : GlobalAddressLiveSizeFormation.Row memory id (sizes id) := state.rows ⟨base,id⟩ member
  generalize sizeEq : sizes id = size at row ⊢
  cases row with
  | localRow other found =>
    have same : other = entry := congrArg Prod.snd (Option.some.inj (found.symm.trans live))
    exact congrArg (fun value => value.allocation.byteSize) same
  | globalRow descriptor absent _ _ _ _ => rw [live] at absent;cases absent

/-- Existing global managed address geometry separates physical windows in
DISTINCT live allocations represented by raw registered inverse rows.
The cursor frontier also derives both allocation-level addressFits clauses.
No inverse index, successful operation, borrow authority or call separation is
assumed. This is not a completeness theorem for ordinary call states; concrete
pointers without inverse-row evidence remain outside this bridge. -/
theorem registered_rows {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (sizes : AllocId → Size)
    (representation : GlobalAddressReuseManagedResources.Post memory addresses sizes)
    (sourceId destinationId : AllocId)
    (sourceEntry destinationEntry : LocalAllocation Provenance BorrowTree K)
    (sourceLive : memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry))
    (destinationLive : memory.live.find? (fun row => row.1 == destinationId) = some (destinationId,destinationEntry))
    (different : sourceId ≠ destinationId)
    (sourceBase sourceOffset len sourceAddress destinationBase destinationOffset destinationAddress : UInt64)
    (sourceMember : (⟨sourceBase,sourceId⟩ : InverseAddressEntry) ∈ addresses.intToPtrMap)
    (destinationMember : (⟨destinationBase,destinationId⟩ : InverseAddressEntry) ∈ addresses.intToPtrMap)
    (sourcePhysical : OrdinaryPhysicalValidity.MutU8Slice sourceEntry.allocation sourceOffset len)
    (destinationPhysical : OrdinaryPhysicalValidity.BoolDestination destinationEntry.allocation destinationOffset)
    (sourceBinding : sourceAddress = sourceBase+sourceOffset)
    (destinationBinding : destinationAddress = destinationBase+destinationOffset) :
    sourceBase.toNat+sourceEntry.allocation.byteSize.bytes.toNat < 2^64 ∧
    destinationBase.toNat+destinationEntry.allocation.byteSize.bytes.toNat < 2^64 ∧
    (len = 0 ∨ sourceAddress.toNat+len.toNat ≤ destinationAddress.toNat ∨
      destinationAddress.toNat+1 ≤ sourceAddress.toNat) := by
  obtain ⟨generation,state⟩ := representation
  obtain ⟨sourceIndex,sourceValid,sourceEqual⟩ := Array.mem_iff_getElem.mp sourceMember
  obtain ⟨destinationIndex,destinationValid,destinationEqual⟩ := Array.mem_iff_getElem.mp destinationMember
  have sourceRow : addresses.intToPtrMap[sourceIndex]? = some ⟨sourceBase,sourceId⟩ := by rw [Array.getElem?_eq_getElem sourceValid,sourceEqual]
  have destinationRow : addresses.intToPtrMap[destinationIndex]? = some ⟨destinationBase,destinationId⟩ := by rw [Array.getElem?_eq_getElem destinationValid,destinationEqual]
  have sourceSize := live_size memory addresses sizes state.resources sourceId sourceEntry sourceBase sourceLive sourceMember
  have destinationSize := live_size memory addresses sizes state.resources destinationId destinationEntry destinationBase destinationLive destinationMember
  have sourceFrontier := state.frontier ⟨sourceBase,sourceId⟩ sourceMember
  have destinationFrontier := state.frontier ⟨destinationBase,destinationId⟩ destinationMember
  dsimp only at sourceFrontier destinationFrontier
  rw [sourceSize] at sourceFrontier
  rw [destinationSize] at destinationFrontier
  have cursorBound := generation.generator.nextBaseAddr.toNat_lt
  have sourceFits : sourceBase.toNat+sourceEntry.allocation.byteSize.bytes.toNat < 2^64 := by omega
  have destinationFits : destinationBase.toNat+destinationEntry.allocation.byteSize.bytes.toNat < 2^64 := by omega
  refine ⟨sourceFits,destinationFits,Or.inr ?_⟩
  have sourceBounds := sourcePhysical.contained
  have destinationBounds := destinationPhysical.contained
  have sourceAddressFits : sourceBase.toNat+sourceOffset.toNat < 2^64 := by omega
  have destinationAddressFits : destinationBase.toNat+destinationOffset.toNat < 2^64 := by omega
  rw [sourceBinding,destinationBinding,UInt64.toNat_add,UInt64.toNat_add,
    Nat.mod_eq_of_lt sourceAddressFits,Nat.mod_eq_of_lt destinationAddressFits]
  have indexDifferent : sourceIndex ≠ destinationIndex := by
    intro equal
    rw [equal] at sourceRow
    have ids := congrArg InverseAddressEntry.allocId (Option.some.inj (sourceRow.symm.trans destinationRow))
    exact different ids
  rcases Nat.lt_or_gt_of_ne indexDifferent with earlier | later
  · have apart := state.resources.apart sourceIndex destinationIndex destinationValid earlier
    simp only [sourceEqual,destinationEqual,sourceSize,destinationSize] at apart
    exact Or.inl (by omega)
  · have apart := state.resources.apart destinationIndex sourceIndex sourceValid later
    simp only [sourceEqual,destinationEqual,sourceSize,destinationSize] at apart
    exact Or.inr (by omega)
/-- Both wildcard hit geometries supply the registered rows internally. -/
theorem separated {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (sizes : AllocId → Size)
    (representation : GlobalAddressReuseManagedResources.Post memory addresses sizes)
    (sourceId destinationId : AllocId)
    (sourceEntry destinationEntry : LocalAllocation Provenance BorrowTree K)
    (sourceLive : memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry))
    (destinationLive : memory.live.find? (fun row => row.1 == destinationId) = some (destinationId,destinationEntry))
    (different : sourceId ≠ destinationId)
    (sourceBase sourceOffset len sourceAddress destinationBase destinationOffset destinationAddress : UInt64)
    (sourceGeometry : WildcardGeneralHitReborrow.Geometry addresses.intToPtrMap sourceAddress sourceBase sourceId sourceEntry.allocation.byteSize)
    (destinationGeometry : WildcardGeneralHitReborrow.Geometry addresses.intToPtrMap destinationAddress destinationBase destinationId destinationEntry.allocation.byteSize)
    (sourcePhysical : OrdinaryPhysicalValidity.MutU8Slice sourceEntry.allocation sourceOffset len)
    (destinationPhysical : OrdinaryPhysicalValidity.BoolDestination destinationEntry.allocation destinationOffset)
    (sourceBinding : sourceAddress = sourceBase+sourceOffset)
    (destinationBinding : destinationAddress = destinationBase+destinationOffset) :
    sourceBase.toNat+sourceEntry.allocation.byteSize.bytes.toNat < 2^64 ∧
    destinationBase.toNat+destinationEntry.allocation.byteSize.bytes.toNat < 2^64 ∧
    (len = 0 ∨ sourceAddress.toNat+len.toNat ≤ destinationAddress.toNat ∨
      destinationAddress.toNat+1 ≤ sourceAddress.toNat) := by
  obtain ⟨_,_,sourceRow⟩ := geometry_row _ _ _ _ _ sourceGeometry
  obtain ⟨_,_,destinationRow⟩ := geometry_row _ _ _ _ _ destinationGeometry
  exact registered_rows memory addresses sizes representation sourceId destinationId sourceEntry destinationEntry sourceLive destinationLive different
    sourceBase sourceOffset len sourceAddress destinationBase destinationOffset destinationAddress
    (Array.mem_of_getElem? sourceRow) (Array.mem_of_getElem? destinationRow) sourcePhysical destinationPhysical sourceBinding destinationBinding

end
end DuplicatePrefix.OrdinaryDistinctAddressBoundary
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.OrdinaryDistinctAddressBoundary." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved distinct address boundary dependency {dependency}"
