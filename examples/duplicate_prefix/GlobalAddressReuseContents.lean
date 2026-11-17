import duplicate_prefix.GlobalAddressAlignedManagedFormation
namespace DuplicatePrefix.GlobalAddressReuseContents
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

open Lean Elab in
elab "source_reuse_ensure" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".ReusePool.ensureSubpool" then some name else none
  let [name] := names | throwError "expected source ensureSubpool"
  Lean.Meta.mkConstWithFreshMVarLevels name

def Contents (pool : ReusePool) (property : ReusableAddress → Prop) : Prop :=
  ∀ bucket ∈ pool.pool, ∀ entry ∈ bucket, property entry

/-- Source ensure_subpool only appends empty buckets, even for arbitrary
alignment indices. It cannot invent or duplicate a reusable address. -/
theorem ensure (pool : ReusePool) (index : Nat) (property : ReusableAddress → Prop)
    (initial : Contents pool property) : Contents (source_reuse_ensure pool index) property := by
  unfold Contents
  unfold_internal ".ReusePool.ensureSubpool"
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  let good : Array (Array ReusableAddress) → Prop := fun buckets => ∀ bucket ∈ buckets, ∀ entry ∈ bucket, property entry
  have step : ∀ buckets, good buckets →
      (∃ final, scan () buckets = .done final ∧ good final) ∨
      ∃ next, scan () buckets = .yield next ∧ good next ∧ index+1-next.size < index+1-buckets.size := by
    intro buckets valid
    by_cases bounded : buckets.size ≤ index
    · refine Or.inr ⟨buckets.push #[],by simp [scan,bounded],?_,?_⟩
      · intro bucket member entry stored
        rcases Array.mem_push.mp member with old | same
        · exact valid bucket old entry stored
        · subst bucket
          simp only [Array.not_mem_empty] at stored
      · simp only [Array.size_push]
        omega
    · exact Or.inl ⟨buckets,by simp [scan,bounded],valid⟩
  exact GeneralBorrowLoop.invariant scan (fun buckets=>index+1-buckets.size) good step pool.pool initial
end DuplicatePrefix.GlobalAddressReuseContents
