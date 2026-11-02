import duplicate_prefix.GlobalAddressBaseCacheGc
namespace DuplicatePrefix.GlobalAddressPhysicalRowCache
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open GlobalAddressBaseCacheFormation GeneralBorrowGcMachineMemoryRetentionLoop
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- Every inverse row in a physical-row history has its source base cache,
including after partial allocation errors, reuse clocks, free and actual GC. -/
theorem invariant {K} [DecidableEq K] (sizes : AllocId → Size)
    {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    (history : GlobalAddressPhysicalRowHistory.History sizes memory addresses) : Cached addresses := by
  induction history with
  | seed memory mode start stop config positive reuse cross addresses actual =>
    obtain ⟨other,source,apart,rows,frontier⟩:=GlobalAddressManagedBumpState.seed memory sizes mode start stop config reuse cross
    have same : other=addresses:=Except.ok.inj (source.symm.trans actual)
    subst other
    have empty : addresses.intToPtrMap=#[] := by
      unfold GlobalAddressState.new ReusePool.new at actual
      unfold_internal_at ".ReusePool.validRate" at actual
      simp only [reuse,cross,Bool.not_true,Bool.false_eq_true,↓reduceIte,beq_self_eq_true,Except.mapError,bind,Except.bind,pure,Except.pure] at actual
      cases actual
      rfl
    intro row member
    rw [empty] at member
    simp only [Array.not_mem_empty] at member
  | insert before id entry fresh ih=>exact ih
  | allocate before generation generationEq id allocation present sizeEq uncached fresh align valid kind thread choices room clockResult ih =>
    obtain ⟨previous,good⟩:=GlobalAddressPhysicalRowHistory.invariant sizes before
    exact complete _ clockResult (assign _ generation good.managed generationEq id allocation.allocation.byteSize align kind thread choices uncached ih)
  | free before id address nonzero size sizeEq position valid row cached align kind thread choice clock ih =>
    exact free _ id size align kind thread choice clock ih
  | expose before p tracking hook ih=>exact expose _ p _ tracking hook ih
  | gc views lens state before ih=>
    obtain ⟨generation,good⟩:=GlobalAddressPhysicalRowHistory.invariant sizes before
    exact GlobalAddressBaseCacheGc.run views lens state ih good.resources.recurring.live.1

/-- Both exact and interior geometry reveal an actual inverse row. Its cache
is obtained from the history rather than repeated as a selected-hit premise. -/
theorem hit_cached {K} [DecidableEq K] (sizes : AllocId → Size)
    {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    (history : GlobalAddressPhysicalRowHistory.History sizes memory addresses)
    (address base : UInt64) (id : AllocId)
    (geometry : WildcardGeneralHitReborrow.Geometry addresses.intToPtrMap address base id (sizes id)) :
    addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩ := by
  have cached:=invariant sizes history
  rcases geometry with ⟨same,position,valid,ordered,present⟩ | ⟨position,partition,present,inside⟩
  all_goals exact cached ⟨base,id⟩ (Array.mem_of_getElem? present)
end DuplicatePrefix.GlobalAddressPhysicalRowCache
