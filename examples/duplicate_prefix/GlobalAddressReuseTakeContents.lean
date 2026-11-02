import duplicate_prefix.GlobalAddressReuseContents
namespace DuplicatePrefix.GlobalAddressReuseTakeContents
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressReuseContents
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.split false

open Lean Elab in
elab "reuse_source " suffix:str : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith suffix.getString then some name else none
  let [name] := names | throwError "expected unique source helper"
  Lean.Meta.mkConstWithFreshMVarLevels name

def Good (property : ReusableAddress → Prop) (size : Size) (result : ReusePoolResult (Option ReusedAddress)) : Prop :=
  Contents result.state property ∧ ∀ used, result.outcome = .ok (some used) →
    ∃ entry, property entry ∧ used.address=entry.address ∧ size.bytes≤entry.size.bytes

theorem no_result (pool : ReusePool) (property : ReusableAddress → Prop) (size : Size) (initial : Contents pool property) :
    Good property size ⟨pool,.ok none⟩ := ⟨initial,by intro used impossible;cases impossible⟩

theorem error_result (pool : ReusePool) (property : ReusableAddress → Prop) (size : Size) (initial : Contents pool property) (error : ReusePoolError) :
    Good property size ⟨pool,.error error⟩ := ⟨initial,by intro used impossible;cases impossible⟩

theorem update (pool : ReusePool) (index : Nat) (bucket : Array ReusableAddress)
    (property : ReusableAddress → Prop) (initial : Contents pool property)
    (replacement : ∀ entry∈bucket,property entry) (next : ReusePool)
    (actual : (reuse_source ".ReusePool.updateSubpool") pool index bucket = .ok next) : Contents next property := by
  unfold_internal_at ".ReusePool.updateSubpool" at actual
  split at actual
  · rename_i bounded
    cases actual
    intro current member entry stored
    rcases Array.mem_or_eq_of_mem_set (w:=bounded) member with old | same
    · exact initial current old entry stored
    · subst current
      exact replacement entry stored
  · cases actual

/-- Complete actual take_addr preserves stored-hole properties and every
returned address comes from an original stored hole large enough for the
request. Errors remain errors; no successful take is an input premise. -/
theorem take (pool : ReusePool) (property : ReusableAddress → Prop) (initial : Contents pool property)
    (reuse cross : Bool) (selection : Nat) (size : Size) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId) :
    Good property size (pool.takeAddr reuse cross selection size align kind thread) := by
  unfold ReusePool.takeAddr
  simp only [Id.run,bind,pure,Id.instMonad]
  split
  · exact no_result pool property size initial
  · split
    · exact error_result pool property size initial _
    · split
      · exact no_result pool property size initial
      · split
        · exact error_result pool property size initial _
        · cases checked : (reuse_source ".ReusePool.checkedPoolIndex") align with
          | error error => exact error_result pool property size initial error
          | ok index =>
            dsimp only
            have kept := ensure pool index property initial
            cases loaded : (reuse_source ".ReusePool.subpoolAt") (source_reuse_ensure pool index) index with
            | error error => exact error_result _ property size kept error
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
              · exact no_result _ property size kept
              · split
                · exact error_result _ property size kept _
                · split
                  · rename_i selectedValid
                    have selectedGood := all bucket[selection] (Array.getElem_mem selectedValid)
                    have erased : ∀ entry ∈ bucket.eraseIdx selection selectedValid, property entry :=
                      fun entry member => all entry (Array.mem_of_mem_eraseIdx member)
                    cases updated : (reuse_source ".ReusePool.updateSubpool") (source_reuse_ensure pool index) index (bucket.eraseIdx selection selectedValid) with
                    | error error => exact error_result _ property size kept error
                    | ok next =>
                      dsimp only
                      have nextGood := update _ index _ property kept erased next updated
                      split
                      · exact error_result next property size nextGood _
                      · rename_i notSmall
                        have fits : size.bytes ≤ bucket[selection].size.bytes := by
                          apply UInt64.le_iff_toNat_le.mpr
                          have noLt : ¬bucket[selection].size.bytes.toNat < size.bytes.toNat := by
                            simpa only [UInt64.lt_iff_toNat_lt] using notSmall
                          omega
                        cases bytes : Align.bytes align with
                        | error error => exact error_result next property size nextGood _
                        | ok alignment =>
                          dsimp only
                          split
                          · exact error_result next property size nextGood _
                          · split
                            · exact error_result next property size nextGood _
                            · refine ⟨nextGood,?_⟩
                              intro used actual
                              cases actual
                              exact ⟨bucket[selection],selectedGood,rfl,fits⟩
                  · exact error_result _ property size kept _
end DuplicatePrefix.GlobalAddressReuseTakeContents
