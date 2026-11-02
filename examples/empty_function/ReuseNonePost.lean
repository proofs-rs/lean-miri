import empty_function.ReuseSuccessBucket
namespace EmptyFunction.ReuseNonePost
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem shape (pool next : ReusePool) (size : Size) (align : Align) (bytes : UInt64)
    (thread : AddressThreadId) (reuse cross : Bool) (selection : Nat)
    (metadata : Align.bytes align = .ok bytes) (normalized : Align.fromBytes bytes = .ok align)
    (actual : pool.takeAddr reuse cross selection size align .other thread = ⟨next,.ok none⟩) :
    next = pool ∨ next = (reuse_actual ".ReusePool.ensureSubpool") pool align.pow2 := by
  have allowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate reuse = true := by
    by_cases permitted : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate reuse = true
    · exact permitted
    · have denied : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate reuse = false := by simpa using permitted
      simp [ReusePool.takeAddr,denied,Id.run,pure,Pure.pure] at actual
  cases reuse with
  | false =>
    simp [ReusePool.takeAddr,allowed,Id.run] at actual
    cases actual
    exact Or.inl rfl
  | true =>
    have crossAllowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross = true := by
      by_cases permitted : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross = true
      · exact permitted
      · have denied : ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross = false := by simpa using permitted
        simp [ReusePool.takeAddr,allowed,denied,Id.run,pure,Pure.pure] at actual
    obtain ⟨bucket,slot⟩ := ReuseEnsure.slot pool align.pow2
    unfold ReusePool.takeAddr at actual
    simp only [show (AddressMemoryKind.other == .stack) = false from rfl,allowed,crossAllowed,
      Bool.not_true,Bool.false_eq_true,↓reduceIte,
      ReuseTake.checked_alignment align bytes metadata normalized,bind,pure] at actual
    revert actual
    unfold_reuse ".ReusePool.subpoolAt"
    unfold_reuse ".ReusePool.getSubpool?"
    intro actual
    simp only [slot,pure,Pure.pure,Except.pure,Id.run] at actual
    simp only [← show ReuseCandidate.candidate bucket size thread cross =
      (reuse_actual ".ReusePool.candidateRange") bucket size thread cross from rfl] at actual
    split at actual
    · cases actual
      exact Or.inr rfl
    · repeat' first | (solve | cases actual) | (split at actual)

/-- A no-hole result preserves current representation, including appended
empty alignment buckets. No probability/capacity premise is supplied. -/
theorem representation (before : WholeCall.State) (generation : AddressGenerationState)
    (current : InputDraft.GenerationRepresentation before generation)
    (next : ReusePool) (size : Size) (align : Align) (bytes : UInt64)
    (thread : AddressThreadId) (reuse cross : Bool) (selection : Nat)
    (metadata : Align.bytes align = .ok bytes) (normalized : Align.fromBytes bytes = .ok align)
    (actual : generation.reusePool.takeAddr reuse cross selection size align .other thread = ⟨next,.ok none⟩) :
    InputDraft.GenerationRepresentation
      (AddressPost.withAddresses before {before.machine.user.addresses with generation := some {generation with reusePool := next}})
      {generation with reusePool := next} := by
  rcases shape generation.reusePool next size align bytes thread reuse cross selection metadata normalized actual with same | same
  · subst next
    simpa only [←current.current,AddressPost.withAddresses] using current
  · subst next
    exact AddressPost.ensure_representation before generation current align.pow2
end EmptyFunction.ReuseNonePost

open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ReuseNonePost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved assigned-success axiom {dependency} in {name}"
