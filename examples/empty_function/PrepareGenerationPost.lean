import empty_function.AddressAssignedSuccessPost
namespace EmptyFunction.PrepareGenerationPost
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Preparing a managed address never removes a hole: only empty alignment
buckets can be appended. This classifies every source outcome, including error. -/
theorem shape (pool after : ReusePool) (size : Size) (align : Align) (bytes : UInt64)
    (thread : AddressThreadId) (reuse cross : Bool)
    (metadata : Align.bytes align = .ok bytes) (normalized : Align.fromBytes bytes = .ok align)
    (result : Except ReusePoolError (Option (Nat × Nat)))
    (actual : pool.prepareTakeAddr reuse cross size align .other thread = ⟨after,result⟩) :
    after = pool ∨ after = (reuse_actual ".ReusePool.ensureSubpool") pool align.pow2 := by
  unfold ReusePool.prepareTakeAddr at actual
  simp only [show (AddressMemoryKind.other == .stack) = false from rfl,Bool.false_eq_true,↓reduceIte,
    ReuseTake.checked_alignment align bytes metadata normalized,bind,pure,Id.run] at actual
  repeat' first
    | (solve | cases actual; first | exact Or.inl rfl | exact Or.inr rfl)
    | (split at actual)

/-- All successful prepare results preserve the full current representation.
The internal success premise adds no resource or future-success assumption. -/
theorem representation (before : WholeCall.State) (generation : AddressGenerationState)
    (current : InputDraft.GenerationRepresentation before generation)
    (after : ReusePool) (size : Size) (align : Align) (bytes : UInt64)
    (thread : AddressThreadId) (reuse cross : Bool)
    (metadata : Align.bytes align = .ok bytes) (normalized : Align.fromBytes bytes = .ok align)
    (result : Except ReusePoolError (Option (Nat × Nat)))
    (actual : generation.reusePool.prepareTakeAddr reuse cross size align .other thread = ⟨after,result⟩) :
    InputDraft.GenerationRepresentation
      (AddressPost.withAddresses before {before.machine.user.addresses with generation := some {generation with reusePool := after}})
      {generation with reusePool := after} := by
  rcases shape generation.reusePool after size align bytes thread reuse cross metadata normalized result actual with same | same
  · subst after
    simpa only [←current.current,AddressPost.withAddresses] using current
  · subst after
    exact AddressPost.ensure_representation before generation current align.pow2
end EmptyFunction.PrepareGenerationPost
open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.PrepareGenerationPost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved prepare-generation axiom {dependency} in {name}"
