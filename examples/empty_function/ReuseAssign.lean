import empty_function.ReuseTake
import empty_function.AddressChoicePlan
import empty_function.InputDraft
import empty_function.ChoiceFloatSupport
namespace EmptyFunction.ReuseAssign
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- The actual reused-hole address assignment and its real post-acquire cache
insertion cannot error under raw current hole/address uniqueness. -/
theorem assigned (addresses : GlobalAddressState) (generation : AddressGenerationState)
    (id : AllocId) (info : AllocationAddressInfo) (bucket : Array ReusableAddress)
    (bytes : UInt64) (cross : Bool) (selection : Nat)
    (managed : addresses.addressMode = .managed) (current : addresses.generation = some generation)
    (uncached : addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (live : info.live = true) (data : info.kind = .liveData) (kind : info.memoryKind = some .other)
    (present : generation.reusePool.pool[info.align.pow2]? = some bucket)
    (metadata : Align.bytes info.align = .ok bytes) (normalized : Align.fromBytes bytes = .ok info.align)
    (reuseAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseRate true = true)
    (crossAllowed : ReusePool.bernoulliChoiceAllowed generation.reusePool.addressReuseCrossThreadRate cross = true)
    (lower : (ReuseCandidate.candidate bucket info.size info.thread cross).1 ≤ selection)
    (upper : selection < (ReuseCandidate.candidate bucket info.size info.thread cross).2)
    (aligned : ∀ row ∈ bucket, row.address % bytes = 0)
    (absent : ∀ row ∈ bucket, ∀ inverse ∈ addresses.intToPtrMap, inverse.address ≠ row.address) :
    ∃ after, AddressChoicePlan.assignedState
      (addresses.addrFromAllocId id (some info) ⟨true,cross,selection,⟨0,by decide⟩⟩) = .ok after := by
  obtain ⟨pool,used,taken,row,member,address⟩ := ReuseTake.take_bucket generation.reusePool bucket
    info.size info.align bytes info.thread cross selection present metadata normalized
    reuseAllowed crossAllowed lower upper aligned
  let stage : GlobalAddressState := {addresses with generation := some {generation with reusePool := pool}}
  have cache : (stage.cacheAddress id used.address).outcome = .ok () := by
    apply RawAddressCache.cache_fresh stage id used.address uncached
    intro inverse stored
    rw [address]
    exact absent row member inverse stored
  unfold GlobalAddressState.addrFromAllocId
  unfold_source_base
  unfold_source_generation
  simp only [uncached,Option.map_none,live,data,kind,managed,current,
    beq_iff_eq,reduceCtorEq,Bool.not_true,↓reduceIte,
    Id.run,pure,taken]
  simp only [←managed]
  change ∃ after, AddressChoicePlan.assignedState
    (match used.clockToAcquire with
    | some clock => ⟨stage,.ok (.acquireRequired id used.address clock)⟩
    | none => match (stage.cacheAddress id used.address).outcome with
      | .ok _ => ⟨(stage.cacheAddress id used.address).state,.ok (.ready used.address)⟩
      | .error error => ⟨(stage.cacheAddress id used.address).state,.error error⟩) = .ok after
  cases clock : used.clockToAcquire <;>
    simp only [AddressChoicePlan.assignedState,cache] <;> exact ⟨_,rfl⟩
/-- Existing raw current pool representation discharges every physical/support
condition above for every source-supported cross-thread/selection response. -/
theorem current_pool (before : WholeCall.State) (generation : AddressGenerationState)
    (representation : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (info : AllocationAddressInfo) (bucket : Array ReusableAddress)
    (cross : Bool) (selection : Nat)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (live : info.live = true) (data : info.kind = .liveData) (kind : info.memoryKind = some .other)
    (present : generation.reusePool.pool[info.align.pow2]? = some bucket)
    (alignment : InputDraft.AlignmentRepresentation info.align)
    (reuseSupport : ChoiceSupply.Supported (.bernoulli .reuse generation.reusePool.addressReuseRate.toBits)
      (.boolean .addressReuse true))
    (crossSupport : ChoiceSupply.Supported (.bernoulli .crossThread generation.reusePool.addressReuseCrossThreadRate.toBits)
      (.boolean .addressCrossThread cross))
    (lower : (ReuseCandidate.candidate bucket info.size info.thread cross).1 ≤ selection)
    (upper : selection < (ReuseCandidate.candidate bucket info.size info.thread cross).2) :
    ∃ after, AddressChoicePlan.assignedState
      (before.machine.user.addresses.addrFromAllocId id (some info) ⟨true,cross,selection,⟨0,by decide⟩⟩) = .ok after := by
  obtain ⟨bytes,metadata,normalized⟩ := alignment
  have exponent := RawGenerator.normalized_exponent info.align bytes normalized
  have canonical := (RawGenerator.align_metadata info.align exponent).1
  have bytesEq : bytes = RawGenerator.alignment info.align := by rw [metadata] at canonical; exact Except.ok.inj canonical
  have poolBound := (Array.getElem?_eq_some_iff.mp present).1
  have bucketAt := (Array.getElem?_eq_some_iff.mp present).2
  apply assigned before.machine.user.addresses generation id info bucket bytes cross selection
    representation.managed representation.current uncached live data kind present metadata normalized
    (ChoiceFloatSupport.allowed_of_supported .reuse _ true representation.reuseRateLower
      representation.reuseRateUpper reuseSupport)
    (ChoiceFloatSupport.allowed_of_supported .crossThread _ cross representation.crossRateLower
      representation.crossRateUpper crossSupport) lower upper
  · intro row member
    have alignment := representation.poolAlignment info.align.pow2 poolBound row (by simpa only [bucketAt] using member)
    apply UInt64.toNat_inj.mp
    change (row.address % bytes).toNat = 0
    rw [bytesEq,UInt64.toNat_mod,RawGenerator.alignment_nat info.align exponent]
    exact alignment
  · intro row member inverse stored
    have absent := representation.poolAbsent bucket (Array.mem_of_getElem? present) row member inverse stored
    exact Ne.symm absent
end EmptyFunction.ReuseAssign
