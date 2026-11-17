import duplicate_prefix.GlobalAddressReuseTakeContents
namespace DuplicatePrefix.GlobalAddressReuseAddContents
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressReuseContents GlobalAddressReuseTakeContents
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.split false

theorem replaced (bucket : Array ReusableAddress) (index : Nat) (entry : ReusableAddress)
    (property : ReusableAddress → Prop) (initial : ∀ old∈bucket,property old) (newGood : property entry)
    (next : Array ReusableAddress) (actual : (reuse_source ".ReusePool.replaceAt") bucket index entry = .ok next) :
    ∀ old∈next,property old := by
  unfold_internal_at ".ReusePool.replaceAt" at actual
  split at actual
  · rename_i valid
    cases actual
    intro old member
    rcases Array.mem_or_eq_of_mem_set (w:=valid) member with past | same
    · exact initial old past
    · subst old;exact newGood
  · cases actual

theorem inserted (bucket : Array ReusableAddress) (index : Nat) (entry : ReusableAddress)
    (property : ReusableAddress → Prop) (initial : ∀ old∈bucket,property old) (newGood : property entry)
    (next : Array ReusableAddress) (actual : (reuse_source ".ReusePool.insertAt") bucket index entry = .ok next) :
    ∀ old∈next,property old := by
  unfold_internal_at ".ReusePool.insertAt" at actual
  split at actual
  · cases actual
    intro old member
    rcases Array.mem_insertIdx.mp member with same | past
    · subst old;exact newGood
    · exact initial old past
  · cases actual

/-- Actual free-pool insertion introduces only the supplied released range,
including capacity replacement and every explicit error prefix. -/
theorem add (pool : ReusePool) (property : ReusableAddress → Prop) (initial : Contents pool property)
    (choice : Bool) (address : UInt64) (size : Size) (align : Align) (kind : AddressMemoryKind)
    (thread : AddressThreadId) (clock : Unit → VClock) (newGood : property ⟨address,size,thread,clock ()⟩) :
    Contents (pool.addAddr choice address size align kind thread clock).state property := by
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
          have kept := ensure pool index property initial
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
            have all:=kept bucket (Array.mem_of_getElem? bucketPresent)
            split
            · cases changed : (reuse_source ".ReusePool.replaceAt") bucket
                (min ((reuse_source ".ReusePool.partitionPoint") bucket (fun entry => (reuse_source ".ReusePool.lessKey") entry.size entry.thread size thread)) (bucket.size-1))
                (⟨address,size,thread,clock ()⟩ : ReusableAddress) with
              | error error => exact kept
              | ok replacement =>
                dsimp only
                have allReplacement:=replaced bucket _ _ property all newGood replacement changed
                cases updated : (reuse_source ".ReusePool.updateSubpool") (source_reuse_ensure pool index) index replacement with
                | error error => exact kept
                | ok next => exact update _ index _ property kept allReplacement next updated
            · cases changed : (reuse_source ".ReusePool.insertAt") bucket
                ((reuse_source ".ReusePool.partitionPoint") bucket (fun entry => (reuse_source ".ReusePool.lessKey") entry.size entry.thread size thread))
                (⟨address,size,thread,clock ()⟩ : ReusableAddress) with
              | error error => exact kept
              | ok replacement =>
                dsimp only
                have allReplacement:=inserted bucket _ _ property all newGood replacement changed
                cases updated : (reuse_source ".ReusePool.updateSubpool") (source_reuse_ensure pool index) index replacement with
                | error error => exact kept
                | ok next => exact update _ index _ property kept allReplacement next updated
end DuplicatePrefix.GlobalAddressReuseAddContents
