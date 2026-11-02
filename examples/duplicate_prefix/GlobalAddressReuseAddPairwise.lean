import duplicate_prefix.GlobalAddressReusePairwiseUpdate
namespace DuplicatePrefix.GlobalAddressReuseAddPairwise
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressReuseContents GlobalAddressReuseTakeContents GlobalAddressReusePairwise
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.split false

theorem replaced_updated (pool : ReusePool) (index : Nat) (bucket : Array ReusableAddress)
    (found : pool.pool[index]?=some bucket) (selected : Nat) (entry : ReusableAddress)
    (initial : Pairwise pool) (separate : Contents pool (Separate entry)) (replacement : Array ReusableAddress)
    (changed : (reuse_source ".ReusePool.replaceAt") bucket selected entry=.ok replacement)
    (next : ReusePool) (updated : (reuse_source ".ReusePool.updateSubpool") pool index replacement=.ok next) : Pairwise next := by
  unfold_internal_at ".ReusePool.replaceAt" at changed
  split at changed
  · rename_i bound
    cases changed
    unfold_internal_at ".ReusePool.updateSubpool" at updated
    split at updated
    · rename_i valid
      cases updated
      exact GlobalAddressReusePairwiseUpdate.replace pool index valid bucket found selected bound entry initial separate
    · cases updated
  · cases changed

theorem inserted_updated (pool : ReusePool) (index : Nat) (bucket : Array ReusableAddress)
    (found : pool.pool[index]?=some bucket) (selected : Nat) (entry : ReusableAddress)
    (initial : Pairwise pool) (separate : Contents pool (Separate entry)) (replacement : Array ReusableAddress)
    (changed : (reuse_source ".ReusePool.insertAt") bucket selected entry=.ok replacement)
    (next : ReusePool) (updated : (reuse_source ".ReusePool.updateSubpool") pool index replacement=.ok next) : Pairwise next := by
  unfold_internal_at ".ReusePool.insertAt" at changed
  split at changed
  · rename_i bound
    cases changed
    unfold_internal_at ".ReusePool.updateSubpool" at updated
    split at updated
    · rename_i valid
      cases updated
      exact GlobalAddressReusePairwiseUpdate.insert pool index valid bucket found selected bound entry initial separate
    · cases updated
  · cases changed

theorem add (pool : ReusePool) (initial : Pairwise pool)
    (choice : Bool) (address : UInt64) (size : Size) (align : Align) (kind : AddressMemoryKind)
    (thread : AddressThreadId) (clock : Unit → VClock) (newSeparate : Contents pool (Separate ⟨address,size,thread,clock ()⟩)) :
    Pairwise (pool.addAddr choice address size align kind thread clock).state := by
  unfold ReusePool.addAddr
  simp only [Id.run,bind,pure,Id.instMonad]
  split
  · exact initial
  · split
    · exact initial
    · split
      · exact initial
      · cases checked : (reuse_source ".ReusePool.checkedPoolIndex") align with
        | error error => exact initial
        | ok index =>
          dsimp only
          have kept := GlobalAddressReusePairwise.ensure pool index initial
          have separate := GlobalAddressReuseContents.ensure pool index _ newSeparate
          cases loaded : (reuse_source ".ReusePool.subpoolAt") (source_reuse_ensure pool index) index with
          | error error => exact kept
          | ok bucket =>
            dsimp only
            have bucketPresent : (source_reuse_ensure pool index).pool[index]? = some bucket := by
              unfold_internal_at ".ReusePool.subpoolAt" at loaded
              unfold_internal_at ".ReusePool.getSubpool?" at loaded
              cases found : (source_reuse_ensure pool index).pool[index]? with
              | none => simp only [found] at loaded;cases loaded
              | some actual => simp only [found] at loaded;cases loaded;rfl
            split
            · cases changed : (reuse_source ".ReusePool.replaceAt") bucket
                (min ((reuse_source ".ReusePool.partitionPoint") bucket (fun entry => (reuse_source ".ReusePool.lessKey") entry.size entry.thread size thread)) (bucket.size-1))
                (⟨address,size,thread,clock ()⟩ : ReusableAddress) with
              | error error => exact kept
              | ok replacement =>
                dsimp only
                cases updated : (reuse_source ".ReusePool.updateSubpool") (source_reuse_ensure pool index) index replacement with
                | error error => exact kept
                | ok next => exact replaced_updated _ index bucket bucketPresent _ _ kept separate replacement changed next updated
            · cases changed : (reuse_source ".ReusePool.insertAt") bucket
                ((reuse_source ".ReusePool.partitionPoint") bucket (fun entry => (reuse_source ".ReusePool.lessKey") entry.size entry.thread size thread))
                (⟨address,size,thread,clock ()⟩ : ReusableAddress) with
              | error error => exact kept
              | ok replacement =>
                dsimp only
                cases updated : (reuse_source ".ReusePool.updateSubpool") (source_reuse_ensure pool index) index replacement with
                | error error => exact kept
                | ok next => exact inserted_updated _ index bucket bucketPresent _ _ kept separate replacement changed next updated
end DuplicatePrefix.GlobalAddressReuseAddPairwise
