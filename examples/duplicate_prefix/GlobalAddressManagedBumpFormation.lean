import duplicate_prefix.GlobalAddressBumpRangeFormation
import duplicate_prefix.GlobalAddressLiveSizeFormation
namespace DuplicatePrefix.GlobalAddressManagedBumpFormation
open Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressRangeFormation GlobalAddressBumpRangeFormation WildcardEmptyFamilyFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def ready (addresses : GlobalAddressState) (generation : AddressGenerationState) (size : Size) (slack : Fin 16) : GlobalAddressState :=
  let generator := next generation.generator size slack
  let pool := if generator.nextBaseAddr > generator.endAddr/2 then generation.reusePool.addressSpaceShortage else generation.reusePool
  {addresses with generation := some ⟨generator,pool⟩}

def info (size : Size) (kind : AddressMemoryKind) (thread : AddressThreadId) : AllocationAddressInfo :=
  ⟨.liveData,true,size,Align.ONE,some kind,thread⟩

def choices (slack : Fin 16) : AddressRandomChoices := ⟨false,false,0,slack⟩

theorem no_reuse (pool : ReusePool) (size : Size) (kind : AddressMemoryKind) (thread : AddressThreadId)
    (allowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate false = true) :
    pool.takeAddr false false 0 size Align.ONE kind thread = ⟨pool,.ok none⟩ := by
  unfold ReusePool.takeAddr
  cases kind <;> simp [allowed,beq_iff_eq]

/-- The numeric placement needed for nonoverlap is derived from the actual
source bump and cursor frontier, rather than assumed by this endpoint. This
managed source branch chooses legal no-reuse and actual Align.ONE. -/
theorem source (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (sizes : AllocId → Size) (initial : Apart addresses.intToPtrMap sizes)
    (frontier : Frontier addresses.intToPtrMap sizes generation.generator)
    (managed : addresses.addressMode = .managed) (generationEq : addresses.generation = some generation)
    (cursor : generation.generator.nextBaseAddr ≠ 0)
    (id : AllocId) (size : Size) (sizeEq : sizes id = size)
    (uncached : addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (kind : AddressMemoryKind) (thread : AddressThreadId) (slack : Fin 16)
    (allowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate false = true)
    (room : Room generation.generator size slack) :
    let staged := ready addresses generation size slack
    let cached := staged.cacheAddress id (base generation.generator slack)
    addresses.addrFromAllocId id (some (info size kind thread)) (choices slack) =
      ⟨cached.state,.ok (.ready (base generation.generator slack))⟩ ∧
    Apart cached.state.intToPtrMap sizes := by
  dsimp only
  have placementFacts := placement addresses.intToPtrMap sizes generation.generator frontier id size sizeEq slack room
  have positive : base generation.generator slack ≠ 0 := by
    intro zero
    have value := base_nat generation.generator size slack room
    rw [zero] at value
    change (0:Nat) = generation.generator.nextBaseAddr.toNat + slack.val at value
    have current : generation.generator.nextBaseAddr.toNat ≠ 0 := by
      intro same
      exact cursor (UInt64.toNat_inj.mp same)
    omega
  have cachedFacts := cache (ready addresses generation size slack) sizes initial id (base generation.generator slack)
    uncached positive addresses.intToPtrMap.size placementFacts.1 placementFacts.2
  refine ⟨?_,cachedFacts.2⟩
  have taken := no_reuse generation.reusePool size kind thread allowed
  have bumped := generated generation.generator size slack room
  unfold GlobalAddressState.addrFromAllocId
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.setGeneration"
  simp only [uncached,Option.map_none,info,choices,managed,generationEq,taken,bumped,
    show (AllocationAddressKind.liveData == AllocationAddressKind.dead) = false from rfl,
    beq_iff_eq,reduceCtorEq,Bool.false_or,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
  simp only [←managed]
  change (match ((ready addresses generation size slack).cacheAddress id (base generation.generator slack)).outcome with
    | .ok _ => (show AddressStateResult AddressAssignment from ⟨((ready addresses generation size slack).cacheAddress id (base generation.generator slack)).state,.ok (.ready (base generation.generator slack))⟩)
    | .error error => (show AddressStateResult AddressAssignment from ⟨((ready addresses generation size slack).cacheAddress id (base generation.generator slack)).state,.error error⟩)) = _
  rw [cachedFacts.1]

end DuplicatePrefix.GlobalAddressManagedBumpFormation
