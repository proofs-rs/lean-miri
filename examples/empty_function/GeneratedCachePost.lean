import empty_function.GeneratedGeometry
import empty_function.AddressPost
namespace EmptyFunction.GeneratedCachePost
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.AddressPost
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

private theorem backing_withAddresses (before : WholeCall.State) (addresses : GlobalAddressState)
    (id : AllocId) (backing : InputDraft.MetadataBacking before id) :
    InputDraft.MetadataBacking (withAddresses before addresses) id := by
  cases backing with
  | live entry row => exact .live entry row
  | global entry row identity => exact .global entry row identity
  | extraFunction row => exact .extraFunction row
  | vaList row => exact .vaList row
  | dead entry row => exact .dead entry row

/-- The actual successful bump and cache preserve current geometry, including
base zero. Exhausted/overflow results are left to the separate error branch. -/
theorem cache (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (target : AllocationInfo) (slack : Fin 16)
    (generator : AddressGenerator) (base : UInt64)
    (actual : generation.generator.generate target.size target.align slack = ⟨generator,.ok base⟩)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (backing : InputDraft.MetadataBacking before id)
    (live : before.machine.memory.isAllocLive id = true)
    (metadata : before.machine.memory.getAllocInfo id = .ok target) :
    let next := {generation with generator}
    let stage := withAddresses before {before.machine.user.addresses with generation := some next}
    InputDraft.GenerationRepresentation
      (withAddresses stage (stage.machine.user.addresses.cacheAddress id base).state) next := by
  dsimp only
  let next := {generation with generator}
  let stageAddr := {before.machine.user.addresses with generation := some next}
  let stage := withAddresses before stageAddr
  change InputDraft.GenerationRepresentation (withAddresses stage (stageAddr.cacheAddress id base).state) next
  obtain ⟨lower,nextNat,_,_⟩ := GeneratedGeometry.generated generation.generator generator target.size target.align slack base actual
  have monotone : generation.generator.nextBaseAddr.toNat ≤ generator.nextBaseAddr.toNat := by omega
  have advanced : InputDraft.GenerationRepresentation stage next :=
    advance_representation before generation representation generator monotone
  by_cases zero : base = 0
  · subst base
    exact cache_zero_representation stage next advanced id uncached
  · have distinct : ∀ row ∈ before.machine.user.addresses.intToPtrMap, row.address ≠ base := by
      intro row member same
      have prior := RawResources.frontier before generation representation row member
      rw [same] at prior
      omega
    apply cache_representation stage next advanced id base uncached zero
      (backing_withAddresses before stageAddr id backing) live distinct
    · intro row member oldInfo newInfo oldQuery newQuery
      have prior := representation.allocatedBeforeCursor row member oldInfo oldQuery
      exact Or.inl (by omega)
    · intro bucket member row stored equal
      have prior := (representation.poolAddresses bucket member row stored).2
      rw [equal] at prior
      omega
    · intro bucket member row stored info query
      have prior := (representation.poolAddresses bucket member row stored).2
      exact Or.inl (by omega)
    · intro info query
      have same : info = target := by
        change before.machine.memory.getAllocInfo id = .ok info at query
        rw [metadata] at query
        exact (Except.ok.inj query).symm
      subst info
      exact Nat.le_of_eq nextNat.symm
end EmptyFunction.GeneratedCachePost
open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.GeneratedCachePost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated-cache axiom {dependency} in {name}"
