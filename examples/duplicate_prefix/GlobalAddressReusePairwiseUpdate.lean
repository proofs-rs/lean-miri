import duplicate_prefix.GlobalAddressReuseInsertedHoles
namespace DuplicatePrefix.GlobalAddressReusePairwiseUpdate
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressReuseContents GlobalAddressReusePairwise
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

theorem symm (a b : ReusableAddress) (separate : Separate a b) : Separate b a := separate.symm

theorem stored (pool : ReusePool) (property : ReusableAddress → Prop) (contents : Contents pool property)
    (slot : Slot) (entry : ReusableAddress) (present : peek pool.pool slot=some entry) : property entry := by
  unfold peek at present
  cases found : pool.pool[slot.1]? with
  | none => simp only [found,Option.bind_none] at present;cases present
  | some bucket =>
    simp only [found,Option.bind_some] at present
    exact contents bucket (Array.mem_of_getElem? found) entry (Array.mem_of_getElem? present)

theorem transport (pool next : ReusePool) (entry : ReusableAddress) (target : Slot) (origin : Slot → Slot)
    (initial : Pairwise pool) (newSeparate : Contents pool (Separate entry))
    (lookup : ∀ slot,peek next.pool slot=if slot=target then some entry else peek pool.pool (origin slot))
    (injective : ∀ left right,left≠target → right≠target → origin left=origin right → left=right) : Pairwise next := by
  intro left right a b one two different
  rw [lookup] at one two
  by_cases l : left=target
  · rw [if_pos l] at one
    cases one
    have r : right≠target := by intro r;exact different (l.trans r.symm)
    rw [if_neg r] at two
    exact stored pool _ newSeparate _ _ two
  · rw [if_neg l] at one
    by_cases r : right=target
    · rw [if_pos r] at two
      cases two
      exact symm _ _ (stored pool _ newSeparate _ _ one)
    · rw [if_neg r] at two
      exact initial _ _ a b one two (fun same=>different (injective left right l r same))

def insertedOrigin (index selected : Nat) (slot : Slot) : Slot :=
  if slot.1=index then (index,if slot.2<selected then slot.2 else slot.2-1) else slot

theorem insert_injective (index selected : Nat) (left right : Slot)
    (l : left≠(index,selected)) (r : right≠(index,selected))
    (same : insertedOrigin index selected left=insertedOrigin index selected right) : left=right := by
  rcases left with ⟨li,le⟩
  rcases right with ⟨ri,re⟩
  by_cases a : li=index <;> by_cases b : ri=index
  · subst li;subst ri
    have ln : le≠selected := by intro e;exact l (by cases e;rfl)
    have rn : re≠selected := by intro e;exact r (by cases e;rfl)
    simp only [insertedOrigin,↓reduceIte,Prod.mk.injEq] at same
    by_cases c : le<selected <;> by_cases d : re<selected <;> simp only [c,d,↓reduceIte] at same
    all_goals congr 1 <;> omega
  · simp only [insertedOrigin,a,b,↓reduceIte,Prod.mk.injEq] at same
    exact False.elim (b same.1.symm)
  · simp only [insertedOrigin,a,b,↓reduceIte,Prod.mk.injEq] at same
    exact False.elim same.1
  · simpa only [insertedOrigin,a,b,↓reduceIte] using same

theorem insert (pool : ReusePool) (index : Nat) (valid : index<pool.pool.size) (bucket : Array ReusableAddress)
    (found : pool.pool[index]?=some bucket) (selected : Nat) (bound : selected≤bucket.size) (entry : ReusableAddress)
    (initial : Pairwise pool) (newSeparate : Contents pool (Separate entry)) :
    Pairwise {pool with pool:=pool.pool.set index (bucket.insertIdx selected entry bound) valid} := by
  apply transport pool _ entry (index,selected) (insertedOrigin index selected) initial newSeparate
  · intro slot
    change peek (pool.pool.set index (bucket.insertIdx selected entry bound) valid) slot= _
    unfold peek
    by_cases same : slot.1=index
    · rw [same,Array.getElem?_set_self valid]
      simp only [Option.bind_some,Array.getElem?_insertIdx bound,insertedOrigin,same,↓reduceIte,found]
      by_cases equal : slot.2=selected
      · have exactSlot : slot=(index,selected) := Prod.ext same equal
        simp only [equal,Nat.lt_irrefl,↓reduceIte,bound,exactSlot]
      · have distinct : slot≠(index,selected) := fun e=>equal (congrArg Prod.snd e)
        simp only [equal,distinct,↓reduceIte,Option.bind_some]
        split <;> rfl
    · rw [Array.getElem?_set_ne valid (Ne.symm same)]
      have distinct : slot≠(index,selected) := fun e=>same (congrArg Prod.fst e)
      simp only [insertedOrigin,same,distinct,↓reduceIte]
  · exact insert_injective index selected

theorem replace (pool : ReusePool) (index : Nat) (valid : index<pool.pool.size) (bucket : Array ReusableAddress)
    (found : pool.pool[index]?=some bucket) (selected : Nat) (bound : selected<bucket.size) (entry : ReusableAddress)
    (initial : Pairwise pool) (newSeparate : Contents pool (Separate entry)) :
    Pairwise {pool with pool:=pool.pool.set index (bucket.set selected entry bound) valid} := by
  apply transport pool _ entry (index,selected) id initial newSeparate
  · intro slot
    change peek (pool.pool.set index (bucket.set selected entry bound) valid) slot= _
    unfold peek
    by_cases same : slot.1=index
    · rw [same,Array.getElem?_set_self valid]
      simp only [Option.bind_some,Array.getElem?_set bound]
      by_cases equal : slot.2=selected
      · have exactSlot : slot=(index,selected) := Prod.ext same equal
        simp only [equal,exactSlot,↓reduceIte]
      · have distinct : slot≠(index,selected) := fun e=>equal (congrArg Prod.snd e)
        simp only [equal,Ne.symm equal,distinct,↓reduceIte,id_eq,same,found,Option.bind_some]
    · rw [Array.getElem?_set_ne valid (Ne.symm same)]
      have distinct : slot≠(index,selected) := fun e=>same (congrArg Prod.fst e)
      simp only [distinct,↓reduceIte,id_eq]
  · intro left right _ _ same;exact same
end DuplicatePrefix.GlobalAddressReusePairwiseUpdate
