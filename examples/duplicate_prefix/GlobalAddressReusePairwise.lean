import duplicate_prefix.GlobalAddressReuseRangeSeed
namespace DuplicatePrefix.GlobalAddressReusePairwise
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressReuseContents
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

abbrev Slot := Nat × Nat

def peek (buckets : Array (Array ReusableAddress)) (slot : Slot) : Option ReusableAddress :=
  buckets[slot.1]?.bind (fun bucket=>bucket[slot.2]?)

def Separate (left right : ReusableAddress) : Prop :=
  left.address.toNat+max 1 left.size.bytes.toNat ≤ right.address.toNat ∨
  right.address.toNat+max 1 right.size.bytes.toNat ≤ left.address.toNat

def Pairwise (pool : ReusePool) : Prop := ∀ left right a b,
  peek pool.pool left=some a → peek pool.pool right=some b → left≠right → Separate a b

theorem push_empty (buckets : Array (Array ReusableAddress)) (slot : Slot) :
    peek (buckets.push #[]) slot=peek buckets slot := by
  unfold peek
  rw [Array.getElem?_push]
  by_cases same : slot.1=buckets.size
  · rw [if_pos same]
    simp only [Option.bind_some,Array.getElem?_empty]
    rw [Array.getElem?_eq_none (by omega)]
    rfl
  · rw [if_neg same]

theorem ensure_peek (pool : ReusePool) (index : Nat) :
    ∀ slot,peek (source_reuse_ensure pool index).pool slot=peek pool.pool slot := by
  unfold_internal ".ReusePool.ensureSubpool"
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  let good : Array (Array ReusableAddress) → Prop := fun buckets=>∀slot,peek buckets slot=peek pool.pool slot
  have step : ∀ buckets,good buckets →
      (∃ final,scan () buckets=.done final ∧ good final) ∨
      ∃ next,scan () buckets=.yield next ∧ good next ∧ index+1-next.size<index+1-buckets.size := by
    intro buckets initial
    by_cases bounded : buckets.size≤index
    · refine Or.inr ⟨buckets.push #[],by simp [scan,bounded],?_,?_⟩
      · intro slot
        exact (push_empty buckets slot).trans (initial slot)
      · simp only [Array.size_push]
        omega
    · exact Or.inl ⟨buckets,by simp [scan,bounded],initial⟩
  exact GeneralBorrowLoop.invariant scan (fun buckets=>index+1-buckets.size) good step pool.pool (fun _=>rfl)

theorem ensure (pool : ReusePool) (index : Nat) (initial : Pairwise pool) : Pairwise (source_reuse_ensure pool index) := by
  intro left right a b one two different
  rw [ensure_peek] at one two
  exact initial left right a b one two different

def lift (index selected : Nat) (slot : Slot) : Slot :=
  if slot.1=index then (slot.1,if slot.2<selected then slot.2 else slot.2+1) else slot

theorem skip_injective (selected left right : Nat)
    (same : (if left<selected then left else left+1)=(if right<selected then right else right+1)) : left=right := by
  by_cases one : left<selected <;> by_cases two : right<selected <;> simp only [one,two,↓reduceIte] at same <;> omega

theorem lift_injective (index selected : Nat) (left right : Slot) (same : lift index selected left=lift index selected right) : left=right := by
  have first : left.1=right.1 := by simpa only [lift,apply_ite Prod.fst,ite_self] using congrArg Prod.fst same
  rcases left with ⟨li,le⟩
  rcases right with ⟨ri,re⟩
  simp only at first
  subst ri
  by_cases equal : li=index
  · simp only [lift,equal,↓reduceIte,Prod.mk.injEq] at same
    exact congrArg (fun n=>(li,n)) (skip_injective selected le re same.2)
  · simpa only [lift,equal,↓reduceIte] using same

theorem erased_peek (pool : ReusePool) (index : Nat) (valid : index<pool.pool.size) (bucket : Array ReusableAddress)
    (stored : pool.pool[index]?=some bucket) (selected : Nat) (selectedValid : selected<bucket.size) (slot : Slot) :
    peek (pool.pool.set index (bucket.eraseIdx selected selectedValid) valid) slot=peek pool.pool (lift index selected slot) := by
  unfold peek
  by_cases same : slot.1=index
  · rw [same,Array.getElem?_set_self valid]
    simp only [Option.bind_some,Array.getElem?_eraseIdx selectedValid]
    simp only [lift,same,↓reduceIte,stored,Option.bind_some]
    split <;> rfl
  · rw [Array.getElem?_set_ne valid (Ne.symm same)]
    simp only [lift,same,↓reduceIte]

/-- Exact source slot injection through erasing a selected pool entry retains
pairwise physical hole separation; a mere membership/subset premise would not
exclude duplicate retained occurrences. -/
theorem erased (pool : ReusePool) (index : Nat) (valid : index<pool.pool.size) (bucket : Array ReusableAddress)
    (stored : pool.pool[index]?=some bucket) (selected : Nat) (selectedValid : selected<bucket.size)
    (initial : Pairwise pool) : Pairwise {pool with pool:=pool.pool.set index (bucket.eraseIdx selected selectedValid) valid} := by
  intro left right a b one two different
  change peek (pool.pool.set index (bucket.eraseIdx selected selectedValid) valid) left=some a at one
  change peek (pool.pool.set index (bucket.eraseIdx selected selectedValid) valid) right=some b at two
  rw [erased_peek pool index valid bucket stored selected selectedValid] at one two
  exact initial _ _ a b one two (fun same=>different (lift_injective index selected left right same))
end DuplicatePrefix.GlobalAddressReusePairwise
