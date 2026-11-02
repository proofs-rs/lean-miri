import empty_function.AddressPost
namespace EmptyFunction.AddressGenerationPost
open Miri Miri.Memory Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem cache_generation (state : GlobalAddressState) (id : AllocId) (address : UInt64) :
    (state.cacheAddress id address).state.generation = state.generation := by
  unfold GlobalAddressState.cacheAddress
  repeat' first | rfl | split


private theorem assigned_generation (result : AddressStateResult AddressAssignment) (after : GlobalAddressState)
    (actual : AddressChoicePlan.assignedState result = .ok after) :
    after.generation = result.state.generation := by
  unfold AddressChoicePlan.assignedState at actual
  split at actual
  · cases actual
  · cases actual
    rfl
  · dsimp only at actual
    split at actual
    · cases actual
    · cases actual
      exact cache_generation _ _ _

/-- An established real assignment can only retain the generator or perform
its one source generate operation. This postcondition covers cached, zero,
reuse/acquire, and bump branches without adding a caller success assumption. -/
theorem generator_shape (state : GlobalAddressState) (generation : AddressGenerationState)
    (id : AllocId) (info : AllocationAddressInfo) (choices : AddressRandomChoices)
    (current : state.generation = some generation) (managed : state.addressMode = .managed)
    (after : GlobalAddressState)
    (actual : AddressChoicePlan.assignedState (state.addrFromAllocId id (some info) choices) = .ok after) :
    ∃ next, after.generation = some next ∧
      (next.generator = generation.generator ∨
        next.generator = (generation.generator.generate info.size info.align choices.slack).state) := by
  have finalGen := assigned_generation (state.addrFromAllocId id (some info) choices) after actual
  unfold GlobalAddressState.addrFromAllocId at actual finalGen
  split at finalGen
  · exact ⟨generation,finalGen.trans current,Or.inl rfl⟩
  · simp only at finalGen
    cases kind : info.memoryKind with
    | none =>
      simp only [kind,Id.run,pure] at finalGen
      exact ⟨generation,finalGen.trans current,Or.inl rfl⟩
    | some memoryKind =>
      simp only [kind,Id.run,pure,managed,current] at finalGen
      split at finalGen
      · exact ⟨generation,finalGen.trans current,Or.inl rfl⟩
      · split at finalGen
        · split at finalGen <;> simp only [cache_generation] at finalGen <;>
            exact ⟨generation,finalGen.trans current,Or.inl rfl⟩
        · split at finalGen
          · exact ⟨_,finalGen,Or.inl rfl⟩
          · split at finalGen
            · exact ⟨_,finalGen,Or.inl rfl⟩
            · split at finalGen <;> simp only [cache_generation] at finalGen <;>
                exact ⟨_,finalGen,Or.inl rfl⟩
          · split at finalGen
            · exact ⟨_,finalGen,Or.inr rfl⟩
            · split at finalGen <;> simp only [cache_generation] at finalGen <;>
                exact ⟨_,finalGen,Or.inr rfl⟩

end EmptyFunction.AddressGenerationPost
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.AddressGenerationPost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved address generator post axiom {dependency} in {name}"
