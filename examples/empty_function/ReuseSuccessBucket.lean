import empty_function.ReuseSuccessPost
namespace EmptyFunction.ReuseSuccessBucket
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- ensureSubpool can append only empty buckets. Actual successful reuse
therefore necessarily came from a bucket present in the original pool. -/
theorem present (pool : ReusePool) (size : Size) (align : Align) (bytes : UInt64)
    (thread : AddressThreadId) (cross : Bool) (selection : Nat) (used : ReusedAddress)
    (metadata : Align.bytes align = .ok bytes) (normalized : Align.fromBytes bytes = .ok align)
    (actual : (pool.takeAddr true cross selection size align .other thread).outcome = .ok (some used)) :
    ∃ bucket, pool.pool[align.pow2]? = some bucket := by
  cases found : pool.pool[align.pow2]? with
  | some bucket => exact ⟨bucket,rfl⟩
  | none =>
    have missing : pool.pool.size ≤ align.pow2 := by
      by_cases bound : align.pow2 < pool.pool.size
      · simp [Array.getElem?_eq_getElem bound] at found
      · omega
    have reuseAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate true = true := by
      by_cases permitted : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate true = true
      · exact permitted
      · have denied : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate true = false := by simpa using permitted
        simp [ReusePool.takeAddr,denied] at actual
    have crossAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross = true := by
      by_cases permitted : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross = true
      · exact permitted
      · have denied : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross = false := by simpa using permitted
        simp [ReusePool.takeAddr,reuseAllowed,denied] at actual
    have empty := ReuseEnsure.empty_at pool align.pow2 missing
    unfold ReusePool.takeAddr at actual
    simp only [show (AddressMemoryKind.other == .stack) = false from rfl,reuseAllowed,crossAllowed,
      Bool.not_true,Bool.false_eq_true,↓reduceIte,
      ReuseTake.checked_alignment align bytes metadata normalized,bind,pure] at actual
    revert actual
    unfold_reuse ".ReusePool.subpoolAt"
    unfold_reuse ".ReusePool.getSubpool?"
    intro actual
    have emptyRange := ReuseCandidate.empty size thread cross
    simp only [ReuseCandidate.candidate] at emptyRange
    simp [empty,emptyRange,Id.run,pure,Pure.pure,Except.pure] at actual
end EmptyFunction.ReuseSuccessBucket
open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ReuseSuccessBucket.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved reuse-bucket axiom {dependency} in {name}"
