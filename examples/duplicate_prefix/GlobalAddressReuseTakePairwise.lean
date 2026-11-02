import duplicate_prefix.GlobalAddressReuseRemaining
namespace DuplicatePrefix.GlobalAddressReuseTakePairwise
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressReuseContents GlobalAddressReuseTakeContents GlobalAddressReuseRemaining
open GlobalAddressReusePairwise (Pairwise)
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.split false

def Good (property : ReusableAddress → Prop) (size : Size) (result : ReusePoolResult (Option ReusedAddress)) : Prop :=
  Pairwise result.state ∧ Contents result.state property ∧ ∀ used,result.outcome=.ok (some used) →
    ∃ entry,property entry ∧ used.address=entry.address ∧ size.bytes≤entry.size.bytes ∧ Remaining result.state entry

theorem no_result (pool : ReusePool) (property : ReusableAddress → Prop) (size : Size)
    (initial : Contents pool property) (apart : Pairwise pool) : Good property size ⟨pool,.ok none⟩ :=
  ⟨apart,initial,by intro used impossible;cases impossible⟩

theorem error_result (pool : ReusePool) (property : ReusableAddress → Prop) (size : Size)
    (initial : Contents pool property) (apart : Pairwise pool) (error : ReusePoolError) : Good property size ⟨pool,.error error⟩ :=
  ⟨apart,initial,by intro used impossible;cases impossible⟩

/-- Actual source take removes the selected physical slot without duplicating
other holes. Every returned range is disjoint from EVERY remaining pool slot,
forming the certificate needed when it becomes a live allocation. -/
theorem take (pool : ReusePool) (property : ReusableAddress → Prop) (initial : Contents pool property) (initialPairwise : Pairwise pool)
    (reuse cross : Bool) (selection : Nat) (size : Size) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId) :
    Good property size (pool.takeAddr reuse cross selection size align kind thread) := by
  unfold ReusePool.takeAddr
  simp only [Id.run,bind,pure,Id.instMonad]
  split
  · exact no_result pool property size initial initialPairwise
  · split
    · exact error_result pool property size initial initialPairwise _
    · split
      · exact no_result pool property size initial initialPairwise
      · split
        · exact error_result pool property size initial initialPairwise _
        · cases checked : (reuse_source ".ReusePool.checkedPoolIndex") align with
          | error error => exact error_result pool property size initial initialPairwise error
          | ok index =>
            dsimp only
            have kept := ensure pool index property initial
            have keptPairwise := GlobalAddressReusePairwise.ensure pool index initialPairwise
            cases loaded : (reuse_source ".ReusePool.subpoolAt") (source_reuse_ensure pool index) index with
            | error error => exact error_result _ property size kept keptPairwise error
            | ok bucket =>
              dsimp only
              have bucketPresent : (source_reuse_ensure pool index).pool[index]? = some bucket := by
                unfold_internal_at ".ReusePool.subpoolAt" at loaded
                unfold_internal_at ".ReusePool.getSubpool?" at loaded
                cases found : (source_reuse_ensure pool index).pool[index]? with
                | none => simp only [found] at loaded;cases loaded
                | some actual => simp only [found] at loaded;cases loaded;rfl
              have all := kept bucket (Array.mem_of_getElem? bucketPresent)
              split
              · exact no_result _ property size kept keptPairwise
              · split
                · exact error_result _ property size kept keptPairwise _
                · split
                  · rename_i selectedValid
                    have selectedGood := all bucket[selection] (Array.getElem_mem selectedValid)
                    have erased : ∀ entry ∈ bucket.eraseIdx selection selectedValid, property entry :=
                      fun entry member => all entry (Array.mem_of_mem_eraseIdx member)
                    cases updated : (reuse_source ".ReusePool.updateSubpool") (source_reuse_ensure pool index) index (bucket.eraseIdx selection selectedValid) with
                    | error error => exact error_result _ property size kept keptPairwise error
                    | ok next =>
                      dsimp only
                      have nextGood := update _ index _ property kept erased next updated
                      have geometry := GlobalAddressReuseRemaining.updated (source_reuse_ensure pool index) index bucket bucketPresent selection selectedValid keptPairwise next updated
                      split
                      · exact error_result next property size nextGood geometry.1 _
                      · rename_i notSmall
                        have fits : size.bytes ≤ bucket[selection].size.bytes := by
                          apply UInt64.le_iff_toNat_le.mpr
                          have noLt : ¬bucket[selection].size.bytes.toNat < size.bytes.toNat := by
                            simpa only [UInt64.lt_iff_toNat_lt] using notSmall
                          omega
                        cases bytes : Align.bytes align with
                        | error error => exact error_result next property size nextGood geometry.1 _
                        | ok alignment =>
                          dsimp only
                          split
                          · exact error_result next property size nextGood geometry.1 _
                          · split
                            · exact error_result next property size nextGood geometry.1 _
                            · refine ⟨geometry.1,nextGood,?_⟩
                              intro used actual
                              cases actual
                              exact ⟨bucket[selection],selectedGood,rfl,fits,geometry.2⟩
                  · exact error_result _ property size kept keptPairwise _
end DuplicatePrefix.GlobalAddressReuseTakePairwise
