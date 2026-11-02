import duplicate_prefix.GlobalAddressAlignedBumpFormation
import duplicate_prefix.GlobalAddressLiveSizeFormation
namespace DuplicatePrefix.GlobalAddressAlignedManagedFormation
open Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressRangeFormation GlobalAddressAlignedBumpFormation WildcardEmptyFamilyFormation
open GlobalAddressBumpRangeFormation (Frontier)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def ready (addresses : GlobalAddressState) (generation : AddressGenerationState) (size : Size) (align : Align) (slack : Fin 16) : GlobalAddressState :=
  let generator := next generation.generator size align slack
  let pool := if generator.nextBaseAddr > generator.endAddr/2 then generation.reusePool.addressSpaceShortage else generation.reusePool
  {addresses with generation := some ⟨generator,pool⟩}

def info (size : Size) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId) : AllocationAddressInfo :=
  ⟨.liveData,true,size,align,some kind,thread⟩

def choices (slack : Fin 16) : AddressRandomChoices := ⟨false,false,0,slack⟩

theorem no_reuse (pool : ReusePool) (size : Size) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId)
    (allowed : ReusePool.bernoulliChoiceAllowed pool.addressReuseRate false = true) :
    pool.takeAddr false false 0 size align kind thread = ⟨pool,.ok none⟩ := by
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
    (id : AllocId) (size : Size) (sizeEq : sizes id = size) (align : Align) (valid : align.pow2≤29)
    (uncached : addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (kind : AddressMemoryKind) (thread : AddressThreadId) (slack : Fin 16)
    (allowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate false = true)
    (room : Room generation.generator size align slack) :
    let staged := ready addresses generation size align slack
    let cached := staged.cacheAddress id (base generation.generator align slack)
    addresses.addrFromAllocId id (some (info size align kind thread)) (choices slack) =
      ⟨cached.state,.ok (.ready (base generation.generator align slack))⟩ ∧
    Apart cached.state.intToPtrMap sizes := by
  dsimp only
  have placementFacts := placement addresses.intToPtrMap sizes generation.generator frontier id size align valid slack room
  have positive : base generation.generator align slack ≠ 0 := by
    intro zero
    have lower := (base_bounds generation.generator size align valid slack room).1
    rw [zero] at lower
    change generation.generator.nextBaseAddr.toNat+slack.val ≤ 0 at lower
    have current : generation.generator.nextBaseAddr.toNat ≠ 0 := by
      intro same
      exact cursor (UInt64.toNat_inj.mp same)
    omega
  have cachedFacts := cache (ready addresses generation size align slack) sizes initial id (base generation.generator align slack)
    uncached positive addresses.intToPtrMap.size placementFacts.1 placementFacts.2
  refine ⟨?_,cachedFacts.2⟩
  have taken := no_reuse generation.reusePool size align kind thread allowed
  have bumped := generated generation.generator size align valid slack room
  unfold GlobalAddressState.addrFromAllocId
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.setGeneration"
  simp only [uncached,Option.map_none,info,choices,managed,generationEq,taken,bumped,
    show (AllocationAddressKind.liveData == AllocationAddressKind.dead) = false from rfl,
    beq_iff_eq,reduceCtorEq,Bool.false_or,Bool.not_true,Bool.false_eq_true,↓reduceIte,Id.run,bind,pure]
  simp only [←managed]
  change (match ((ready addresses generation size align slack).cacheAddress id (base generation.generator align slack)).outcome with
    | .ok _ => (show AddressStateResult AddressAssignment from ⟨((ready addresses generation size align slack).cacheAddress id (base generation.generator align slack)).state,.ok (.ready (base generation.generator align slack))⟩)
    | .error error => (show AddressStateResult AddressAssignment from ⟨((ready addresses generation size align slack).cacheAddress id (base generation.generator align slack)).state,.error error⟩)) = _
  rw [cachedFacts.1]

end DuplicatePrefix.GlobalAddressAlignedManagedFormation
