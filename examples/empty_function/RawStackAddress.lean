import empty_function.RawGenerator
import empty_function.RawAddressCache
namespace EmptyFunction.RawStackAddress
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

/-- All legal slack values successfully generate and cache a fresh stack base
from numeric room and the current indexed-base frontier. -/
theorem assigned (state : GlobalAddressState) (generation : AddressGenerationState)
    (id : AllocId) (info : AllocationAddressInfo) (choices : AddressRandomChoices)
    (managed : state.addressMode = .managed)
    (current : state.generation = some generation)
    (uncached : state.baseAddr.find? (fun row => row.allocId == id) = none)
    (live : info.live = true) (data : info.kind = .liveData)
    (stack : info.memoryKind = some .stack)
    (alignment : info.align.pow2 ≤ 29)
    (room : RawGenerator.Room generation.generator info.size info.align choices.slack)
    (positive : 0 < generation.generator.nextBaseAddr.toNat)
    (frontier : ∀ row ∈ state.intToPtrMap,
      row.address.toNat < generation.generator.nextBaseAddr.toNat) :
    (state.addrFromAllocId id (some info) choices).outcome =
      .ok (.ready (RawGenerator.base generation.generator info.align choices.slack)) := by
  have bounds := RawGenerator.base_bounds generation.generator info.size info.align alignment choices.slack room
  have nonzero : RawGenerator.base generation.generator info.align choices.slack ≠ 0 := by
    intro zero
    rw [zero] at bounds
    change _ ≤ 0 ∧ _ at bounds
    omega
  have afterAll : ∀ row ∈ state.intToPtrMap,
      row.address < RawGenerator.base generation.generator info.align choices.slack := by
    intro row member
    apply UInt64.lt_iff_toNat_lt.mpr
    have earlier := frontier row member
    omega
  have cache (next : AddressGenerationState) :
      (({state with generation := some next} : GlobalAddressState).cacheAddress id
        (RawGenerator.base generation.generator info.align choices.slack)).outcome = .ok () :=
    RawAddressCache.cache_after _ id _ uncached nonzero afterAll
  have generated := RawGenerator.generated generation.generator info.size info.align alignment choices.slack room
  unfold GlobalAddressState.addrFromAllocId
  unfold_source_base
  unfold_source_generation
  simp only [uncached,Option.map_none,live,data,stack,managed,current,
    beq_self_eq_true,Bool.not_true,↓reduceIte,
    ReusePool.takeAddr,Id.run,pure,beq_iff_eq,generated]
  simp only [← managed, cache]
  simp
end EmptyFunction.RawStackAddress

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.RawStackAddress." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved raw address proof axiom {dependency} in {name}"
