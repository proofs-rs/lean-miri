import empty_function.GeneratedCachePost
namespace EmptyFunction.GeneratedShortagePost
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open EmptyFunction.AddressPost
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

private theorem backing_withAddresses (before : WholeCall.State) (addresses : GlobalAddressState)
    (id : AllocId) (backing : InputDraft.MetadataBacking before id) :
    InputDraft.MetadataBacking (withAddresses before addresses) id := by
  cases backing with
  | live entry row => exact .live entry row
  | global entry row identity => exact .global entry row identity
  | extraFunction row => exact .extraFunction row
  | vaList row => exact .vaList row
  | dead entry row => exact .dead entry row

def next (generation : AddressGenerationState) (generator : AddressGenerator) : AddressGenerationState :=
  {generation with generator, reusePool :=
    if generator.nextBaseAddr > generator.endAddr / 2 then generation.reusePool.addressSpaceShortage else generation.reusePool}

/-- Actual successful generation and its source shortage-rate update preserve
geometry before caching. No request-wide maximum or capacity premise occurs. -/
theorem cache (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (target : AllocationInfo) (slack : Fin 16)
    (generator : AddressGenerator) (base : UInt64)
    (actual : generation.generator.generate target.size target.align slack = ⟨generator,.ok base⟩)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (backing : InputDraft.MetadataBacking before id)
    (live : before.machine.memory.isAllocLive id = true)
    (metadata : before.machine.memory.getAllocInfo id = .ok target) :
    let stage := withAddresses before {before.machine.user.addresses with generation := some (next generation generator)}
    InputDraft.GenerationRepresentation
      (withAddresses stage (stage.machine.user.addresses.cacheAddress id base).state) (next generation generator) := by
  dsimp only
  by_cases shortage : generator.nextBaseAddr > generator.endAddr / 2
  · let shortGen := {generation with reusePool := generation.reusePool.addressSpaceShortage}
    let shortAddr := {before.machine.user.addresses with generation := some shortGen}
    let shortBefore := withAddresses before shortAddr
    have prior : InputDraft.GenerationRepresentation shortBefore shortGen :=
      shortage_representation before generation representation
    have result := GeneratedCachePost.cache shortBefore shortGen prior id target slack generator base actual
      uncached (backing_withAddresses before shortAddr id backing) live metadata
    simpa only [next,shortage,↓reduceIte,shortBefore,shortAddr,shortGen,withAddresses] using result
  · have result := GeneratedCachePost.cache before generation representation id target slack generator base actual
      uncached backing live metadata
    simpa only [next,shortage,↓reduceIte] using result
end EmptyFunction.GeneratedShortagePost

open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.GeneratedShortagePost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved assigned-success axiom {dependency} in {name}"
