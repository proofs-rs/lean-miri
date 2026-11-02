import duplicate_prefix.GlobalAddressLocalManaged
import duplicate_prefix.GlobalAddressPhysicalRowCache
namespace DuplicatePrefix.GlobalAddressPhysicalLocalRows
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressLocalRowFormation GeneralBorrowGcMachineMemoryRetentionLoop
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- This history creates inverse identities only by address assignment to
actual local allocation rows. Its stronger invariant rules out a hidden
MEMORY/STATIC supplier branch for a selected exposed inverse hit. -/
theorem invariant {K} [DecidableEq K] (sizes : AllocId→Size)
    {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    (history : GlobalAddressPhysicalRowHistory.History sizes memory addresses) : Rows memory addresses.intToPtrMap sizes := by
  induction history with
  | seed memory mode start stop config positive reuse cross addresses actual=>
    have empty : addresses.intToPtrMap=#[] := by
      unfold GlobalAddressState.new ReusePool.new at actual
      unfold_internal_at ".ReusePool.validRate" at actual
      simp only [reuse,cross,Bool.not_true,Bool.false_eq_true,↓reduceIte,beq_self_eq_true,Except.mapError,bind,Except.bind,pure,Except.pure] at actual
      cases actual
      rfl
    intro row member
    rw [empty] at member
    simp only [Array.not_mem_empty] at member
  | insert before id entry fresh ih=>
    intro row member
    apply insert_other _ id row.allocId entry
    · intro same
      apply fresh
      exact List.mem_map.mpr ⟨row,by simpa using member,same⟩
    · exact ih row member
  | allocate before generation generationEq id allocation present sizeEq uncached fresh align valid kind thread choices room clockResult ih=>
    obtain ⟨previous,good⟩:=GlobalAddressPhysicalRowHistory.invariant sizes before
    exact GlobalAddressLocalManaged.complete _ _ generation sizes ih good.managed generationEq id allocation present sizeEq uncached align kind thread choices clockResult
  | free before id address nonzero size sizeEq position valid row cached align kind thread choice clock ih=>
    rename_i previousMemory previousAddresses
    obtain ⟨generation,good⟩:=GlobalAddressPhysicalRowHistory.invariant sizes before
    have injective : ∀ (i : Nat) (hi:i<previousAddresses.intToPtrMap.size) (j : Nat) (hj:j<previousAddresses.intToPtrMap.size),
        previousAddresses.intToPtrMap[i].allocId=previousAddresses.intToPtrMap[j].allocId → i=j := by
      intro i hi j hj same
      apply good.resources.recurring.unique.eq_of_getElem_eq (by simpa using hi) (by simpa using hj)
      simpa using same
    have different:=GlobalAddressFreeHistoryFormation.free_shrinks_live _ (fun _=>True)
      ⟨fun _ _=>True.intro,fun _ _=>True.intro⟩ id address position valid good.resources.recurring.ordered row cached injective size align kind thread choice clock
    intro current member
    have old:=(GlobalAddressFreeHistoryFormation.free_subsets _ id size align kind thread choice clock).1 current member
    exact remove_other _ id current.allocId (different.1 current member).2 _ (ih current old)
  | expose before p tracking hook ih=>
    rw [GlobalAddressExposureFormation.expose_inverse]
    exact ih
  | gc views lens state before ih=>
    have next:=GlobalAddressLocalGc.run_preserves (MachineGCRoots.hooks views lens) state _ sizes ih
    have frame:=GlobalAddressGcFrames.run_frame views lens state
    rw [frame.1]
    exact next

/-- The selected exposed exact/interior row is genuinely local and has the
history's recorded size; its base cache is also derived from source recurrence. -/
theorem hit {K} [DecidableEq K] (sizes : AllocId→Size)
    {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    (history : GlobalAddressPhysicalRowHistory.History sizes memory addresses)
    (address base : UInt64) (id : AllocId)
    (geometry : WildcardGeneralHitReborrow.Geometry addresses.intToPtrMap address base id (sizes id)) :
    ∃entry,memory.live.find? (fun row=>row.1==id)=some (id,entry) ∧
      sizes id=entry.allocation.byteSize ∧
      addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩ := by
  have cached:=GlobalAddressPhysicalRowCache.hit_cached sizes history address base id geometry
  have rows:=invariant sizes history
  have localRow : Row memory id (sizes id) := by
    rcases geometry with ⟨same,position,valid,ordered,present⟩ | ⟨position,partition,present,inside⟩
    all_goals exact rows ⟨base,id⟩ (Array.mem_of_getElem? present)
  obtain ⟨entry,present,sizeEq⟩:=localRow
  exact ⟨entry,present,sizeEq,cached⟩
end DuplicatePrefix.GlobalAddressPhysicalLocalRows
