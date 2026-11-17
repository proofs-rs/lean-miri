import duplicate_prefix.CurrentCallConversionCacheFrames
import duplicate_prefix.GlobalAddressReuseResources

namespace DuplicatePrefix.CurrentCallConversionInfoRows
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Converter-internal size rows permit every actual nondead metadata kind,
including function, va-list, vtable and typeId. They are not a caller domain. -/
def InfoRows {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (entries : Array InverseAddressEntry) (sizes : AllocId→Size) : Prop :=
  ∀row∈entries,∃info,memory.getAllocInfo row.allocId=.ok info ∧info.kind≠.dead ∧info.size=sizes row.allocId

/-- Metadata remains unchanged during root/base-cache formation. -/
def sizes {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId) : Size :=
  (((memory.getAllocInfo id).toOption).map AllocationInfo.size).getD Size.ZERO

theorem queried_size {K : Type} {memory : MemoryState Provenance BorrowTree K} {id : AllocId}
    {info : AllocationInfo} (actual : memory.getAllocInfo id=.ok info) : sizes memory id=info.size := by
  simp only [sizes,actual,Except.toOption,Option.map_some,Option.getD_some]

private theorem data_row {K : Type} {memory : MemoryState Provenance BorrowTree K} {id : AllocId} {size : Size}
    (row : GlobalAddressLiveSizeFormation.Row memory id size) :
    ∃info,memory.getAllocInfo id=.ok info ∧info.kind≠.dead ∧info.size=size := by
  cases row with
  | localRow entry present =>
    refine ⟨⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩,?_,?_,rfl⟩
    · simp only [MemoryState.getAllocInfo,present];rfl
    · intro impossible;cases impossible
  | globalRow descriptor absent noFunction noVaList present kind =>
    unfold MemoryState.hasVaListId at noVaList
    refine ⟨⟨descriptor.size,descriptor.align,.liveData,descriptor.mutability⟩,?_,?_,rfl⟩
    · simp only [MemoryState.getAllocInfo,absent,noFunction,noVaList,present,Bool.false_eq_true,↓reduceIte]
      rcases kind with kind | kind <;> rw [kind] <;> rfl
    · intro impossible;cases impossible

/-- The initial stronger data-row certificate embeds pointwise; its sizes can
be replaced by actual getAllocInfo sizes on every stored inverse row. -/
theorem embed {K : Type} {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    {oldSizes : AllocId→Size} (initial : GlobalAddressRangeResources.State memory addresses oldSizes) :
    InfoRows memory addresses.intToPtrMap (sizes memory) ∧
      (∀row∈addresses.intToPtrMap,oldSizes row.allocId=sizes memory row.allocId) := by
  constructor
  · intro row member
    obtain ⟨info,actual,live,_⟩:=data_row (initial.rows row member)
    exact ⟨info,actual,live,(queried_size actual).symm⟩
  · intro row member
    obtain ⟨info,actual,_,equal⟩:=data_row (initial.rows row member)
    exact equal.symm.trans (queried_size actual).symm

/-- Adding a real target metadata row requires no memory/static-only class
and no inverse allocation-ID freshness; actual sizes are canonical. -/
theorem insert {K : Type} {memory : MemoryState Provenance BorrowTree K}
    (entries : Array InverseAddressEntry) (initial : InfoRows memory entries (sizes memory))
    (id : AllocId) (target : GlobalAddressLiveErrorExclusion.Supplier memory id)
    (address : UInt64) (cut : Nat) (bounded : cut≤entries.size) :
    InfoRows memory (entries.insertIdx cut ⟨address,id⟩ bounded) (sizes memory) := by
  intro row member
  rcases Array.mem_insertIdx.mp member with equal | old
  · subst row
    obtain ⟨info,actual,live⟩:=GlobalAddressLiveErrorExclusion.metadata_of_supplier memory id target
    exact ⟨info,actual,live,(queried_size actual).symm⟩
  · exact initial row old

/-- Rebase only the OLD stored rows; no claim about arbitrary uncached IDs is
needed to retain physical separation. -/
theorem apart {K : Type} {memory : MemoryState Provenance BorrowTree K}
    (entries : Array InverseAddressEntry) (oldSizes : AllocId→Size)
    (equal : ∀row∈entries,oldSizes row.allocId=sizes memory row.allocId)
    (initial : WildcardEmptyFamilyFormation.Apart entries oldSizes) :
    WildcardEmptyFamilyFormation.Apart entries (sizes memory) := by
  intro left right valid less
  have leftValid : left<entries.size:=by omega
  have member:=Array.getElem_mem leftValid
  rw [←equal entries[left] member]
  exact initial left right valid less

theorem frontier {K : Type} {memory : MemoryState Provenance BorrowTree K}
    (entries : Array InverseAddressEntry) (oldSizes : AllocId→Size)
    (equal : ∀row∈entries,oldSizes row.allocId=sizes memory row.allocId)
    (generator : AddressGenerator) (initial : GlobalAddressBumpRangeFormation.Frontier entries oldSizes generator) :
    GlobalAddressBumpRangeFormation.Frontier entries (sizes memory) generator := by
  intro row member
  rw [←equal row member]
  exact initial row member

theorem holes {K : Type} {memory : MemoryState Provenance BorrowTree K}
    (entries : Array InverseAddressEntry) (oldSizes : AllocId→Size)
    (equal : ∀row∈entries,oldSizes row.allocId=sizes memory row.allocId)
    (pool : ReusePool) (initial : GlobalAddressReuseContents.Contents pool (GlobalAddressReuseHoleGeometry.Hole entries oldSizes)) :
    GlobalAddressReuseContents.Contents pool (GlobalAddressReuseHoleGeometry.Hole entries (sizes memory)) := by
  intro bucket stored entry member
  have old:=initial bucket stored entry member
  refine ⟨old.1,?_⟩
  intro row present
  rw [←equal row present]
  exact old.2 row present

end DuplicatePrefix.CurrentCallConversionInfoRows
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallConversionInfoRows" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved converter info-size dependency {dependency}"
