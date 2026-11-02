import empty_function.ReuseTake
namespace EmptyFunction.ReuseEnsure
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Source expansion only appends empty buckets. This handles previously
absent alignment indices without requiring the current pool to be prefilled. -/
theorem absent (pool : ReusePool) (index : Nat) (missing : pool.pool.size ≤ index) :
    (reuse_actual ".ReusePool.ensureSubpool") pool index =
      {pool with pool := pool.pool ++ Array.replicate (index+1-pool.pool.size) #[]} := by
  unfold_reuse ".ReusePool.ensureSubpool"
  simp only [Id.run,bind,pure,Id.instMonad,ForIn.forIn]
  name_range_scan
  let invariant : Array (Array ReusableAddress) → Prop := fun entries =>
    pool.pool.size ≤ entries.size ∧ entries.size ≤ index+1 ∧
      entries = pool.pool ++ Array.replicate (entries.size-pool.pool.size) #[]
  let final : Array (Array ReusableAddress) → Prop := fun entries =>
    entries = pool.pool ++ Array.replicate (index+1-pool.pool.size) #[]
  have step : ∀ entries, invariant entries →
      (∃ done, scan () entries = .done done ∧ final done) ∨
      ∃ next, scan () entries = .yield next ∧ invariant next ∧
        index+1-next.size < index+1-entries.size := by
    intro entries good
    obtain ⟨lower,upper,shape⟩ := good
    by_cases grow : entries.size ≤ index
    · refine .inr ⟨entries.push #[],by simp [scan,grow],?_,?_⟩
      · refine ⟨by simp only [Array.size_push];omega,by simp only [Array.size_push];omega,?_⟩
        have count : entries.size+1-pool.pool.size = (entries.size-pool.pool.size)+1 := by omega
        rw [Array.size_push,count,Array.replicate_succ,Array.append_push,←shape]
      · simp only [Array.size_push]
        omega
    · refine .inl ⟨entries,by simp [scan,grow],?_⟩
      have size : entries.size = index+1 := by omega
      simpa only [final,size] using shape
  have finished := RawAddressCache.loop_finished scan (fun entries => index+1-entries.size)
    invariant final step pool.pool ⟨Nat.le_refl _,by omega,by simp⟩
  rw [finished]
theorem empty_at (pool : ReusePool) (index : Nat) (missing : pool.pool.size ≤ index) :
    ((reuse_actual ".ReusePool.ensureSubpool") pool index).pool[index]? = some #[] := by
  rw [absent pool index missing]
  simp only
  rw [Array.getElem?_append]
  have outside : ¬index < pool.pool.size := by omega
  have residual : index-pool.pool.size < index+1-pool.pool.size := by omega
  simp only [outside,↓reduceIte,Array.getElem?_replicate,residual]
theorem slot (pool : ReusePool) (index : Nat) :
    ∃ bucket, ((reuse_actual ".ReusePool.ensureSubpool") pool index).pool[index]? = some bucket := by
  by_cases bounded : index < pool.pool.size
  · refine ⟨pool.pool[index],?_⟩
    rw [ReuseTake.ensure_present pool index bounded]
    exact Array.getElem?_eq_getElem bounded
  · exact ⟨#[],empty_at pool index (by omega)⟩

/-- All current pool lengths are admitted. The real prepare prefix always
loads a bucket, appending empty buckets only when the alignment was absent. -/
theorem prepare (pool : ReusePool) (size : Size) (align : Align) (bytes : UInt64)
    (thread : AddressThreadId) (cross : Bool)
    (metadata : Align.bytes align = .ok bytes) (normalized : Align.fromBytes bytes = .ok align)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate true = true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross = true) :
    ∃ bucket,
      ((reuse_actual ".ReusePool.ensureSubpool") pool align.pow2).pool[align.pow2]? = some bucket ∧
      pool.prepareTakeAddr true cross size align .other thread =
        ⟨(reuse_actual ".ReusePool.ensureSubpool") pool align.pow2,
          .ok (if (ReuseCandidate.candidate bucket size thread cross).2 ==
            (ReuseCandidate.candidate bucket size thread cross).1 then none
            else some (ReuseCandidate.candidate bucket size thread cross))⟩ := by
  obtain ⟨bucket,present⟩ := slot pool align.pow2
  refine ⟨bucket,present,?_⟩
  unfold ReusePool.prepareTakeAddr
  simp only [show (AddressMemoryKind.other == .stack) = false from rfl,reuseAllowed,crossAllowed,
    Bool.not_true,Bool.false_eq_true,↓reduceIte,
    ReuseTake.checked_alignment align bytes metadata normalized,bind,pure]
  unfold_reuse ".ReusePool.subpoolAt"
  unfold_reuse ".ReusePool.getSubpool?"
  simp only [present]
  change (if (ReuseCandidate.candidate bucket size thread cross).2 ==
      (ReuseCandidate.candidate bucket size thread cross).1 then _ else _) = _
  split <;> rfl
theorem rates (pool : ReusePool) (index : Nat) :
    ((reuse_actual ".ReusePool.ensureSubpool") pool index).addressReuseRate = pool.addressReuseRate ∧
    ((reuse_actual ".ReusePool.ensureSubpool") pool index).addressReuseCrossThreadRate = pool.addressReuseCrossThreadRate := by
  by_cases bounded : index < pool.pool.size
  · rw [ReuseTake.ensure_present pool index bounded]
    exact ⟨rfl,rfl⟩
  · rw [absent pool index (by omega)]
    exact ⟨rfl,rfl⟩
end EmptyFunction.ReuseEnsure
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ReuseEnsure.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved reuse ensure axiom {dependency} in {name}"
