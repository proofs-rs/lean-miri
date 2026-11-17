import duplicate_prefix.GlobalAddressReusePairwise
namespace DuplicatePrefix.GlobalAddressReuseRemaining
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressReusePairwise GlobalAddressReuseTakeContents
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

def Remaining (pool : ReusePool) (entry : ReusableAddress) : Prop :=
  ∀ slot other,peek pool.pool slot=some other → Separate entry other

theorem lift_ne_selected (index selected : Nat) (slot : Slot) : lift index selected slot≠(index,selected) := by
  rcases slot with ⟨bi,ei⟩
  intro same
  by_cases equal : bi=index
  · simp only [lift,equal,↓reduceIte,Prod.mk.injEq] at same
    by_cases before : ei<selected <;> simp only [before,↓reduceIte] at same <;> omega
  · simp only [lift,equal,↓reduceIte] at same
    exact equal (congrArg Prod.fst same)

theorem erased_remaining (pool : ReusePool) (index : Nat) (valid : index<pool.pool.size) (bucket : Array ReusableAddress)
    (stored : pool.pool[index]?=some bucket) (selected : Nat) (selectedValid : selected<bucket.size)
    (initial : Pairwise pool) : Remaining {pool with pool:=pool.pool.set index (bucket.eraseIdx selected selectedValid) valid} bucket[selected] := by
  have selectedPresent : peek pool.pool (index,selected)=some bucket[selected] := by
    simp only [peek,stored,Option.bind_some,Array.getElem?_eq_getElem selectedValid]
  intro slot other present
  change peek (pool.pool.set index (bucket.eraseIdx selected selectedValid) valid) slot=some other at present
  rw [erased_peek pool index valid bucket stored selected selectedValid] at present
  exact initial (index,selected) _ _ _ selectedPresent present (Ne.symm (lift_ne_selected index selected slot))

theorem updated (pool : ReusePool) (index : Nat) (bucket : Array ReusableAddress)
    (stored : pool.pool[index]?=some bucket) (selected : Nat) (selectedValid : selected<bucket.size)
    (initial : Pairwise pool) (next : ReusePool)
    (actual : (reuse_source ".ReusePool.updateSubpool") pool index (bucket.eraseIdx selected selectedValid)=.ok next) :
    Pairwise next ∧ Remaining next bucket[selected] := by
  unfold_internal_at ".ReusePool.updateSubpool" at actual
  split at actual
  · rename_i valid
    cases actual
    exact ⟨erased pool index valid bucket stored selected selectedValid initial,
      erased_remaining pool index valid bucket stored selected selectedValid initial⟩
  · cases actual
end DuplicatePrefix.GlobalAddressReuseRemaining
