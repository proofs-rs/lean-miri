import empty_function.AddressPost
import empty_function.ReuseAssign
namespace EmptyFunction.ReuseSuccessPost
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Invert the actual successful hole selection. Illegal probability choices
and candidate indices are errors; no readiness or margin is assumed. -/
theorem take_conditions (pool : ReusePool) (bucket : Array ReusableAddress)
    (size : Size) (align : Align) (bytes : UInt64) (thread : AddressThreadId)
    (cross : Bool) (selection : Nat) (used : ReusedAddress)
    (present : pool.pool[align.pow2]? = some bucket)
    (metadata : Align.bytes align = .ok bytes) (normalized : Align.fromBytes bytes = .ok align)
    (actual : (pool.takeAddr true cross selection size align .other thread).outcome = .ok (some used)) :
    ReusePool.bernoulliChoiceAllowed pool.addressReuseRate true = true ∧
    ReusePool.bernoulliChoiceAllowed pool.addressReuseCrossThreadRate cross = true ∧
    (ReuseCandidate.candidate bucket size thread cross).1 ≤ selection ∧
    selection < (ReuseCandidate.candidate bucket size thread cross).2 := by
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
  refine ⟨reuseAllowed,crossAllowed,?_⟩
  have bounded := (Array.getElem?_eq_some_iff.mp present).1
  unfold ReusePool.takeAddr at actual
  simp only [show (AddressMemoryKind.other == .stack) = false from rfl,reuseAllowed,crossAllowed,
    Bool.not_true,Bool.false_eq_true,↓reduceIte,
    ReuseTake.checked_alignment align bytes metadata normalized,bind,pure,
    ReuseTake.ensure_present pool align.pow2 bounded] at actual
  revert actual
  unfold_reuse ".ReusePool.subpoolAt"
  unfold_reuse ".ReusePool.getSubpool?"
  intro actual
  simp only [present,pure,Pure.pure,Except.pure] at actual
  simp only [← show ReuseCandidate.candidate bucket size thread cross =
    (reuse_actual ".ReusePool.candidateRange") bucket size thread cross from rfl] at actual
  have nonempty : (ReuseCandidate.candidate bucket size thread cross).2 ≠
      (ReuseCandidate.candidate bucket size thread cross).1 := by
    intro empty
    simp [empty,Id.run] at actual
  have legal : ¬(selection < (ReuseCandidate.candidate bucket size thread cross).1 ∨
      selection ≥ (ReuseCandidate.candidate bucket size thread cross).2) := by
    intro bad
    have decision : (selection < (ReuseCandidate.candidate bucket size thread cross).1 ||
        selection ≥ (ReuseCandidate.candidate bucket size thread cross).2) = true := by simpa using bad
    simp [nonempty,decision,Id.run] at actual
  omega
/-- Successful actual reuse preserves full current address geometry. All
probability/index premises of the earlier source proof are inferred above. -/
theorem representation (before : WholeCall.State) (generation : AddressGenerationState)
    (current : InputDraft.GenerationRepresentation before generation)
    (id : AllocId) (target : AllocationInfo) (thread : AddressThreadId)
    (bucket : Array ReusableAddress) (cross : Bool) (selection : Nat) (slack : Fin 16)
    (used : ReusedAddress) (after : GlobalAddressState)
    (uncached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = none)
    (backing : InputDraft.MetadataBacking before id)
    (live : before.machine.memory.isAllocLive id = true)
    (metadata : before.machine.memory.getAllocInfo id = .ok target)
    (present : generation.reusePool.pool[target.align.pow2]? = some bucket)
    (alignment : InputDraft.AlignmentRepresentation target.align)
    (taken : (generation.reusePool.takeAddr true cross selection target.size target.align .other thread).outcome =
      .ok (some used))
    (actual : AddressChoicePlan.assignedState (before.machine.user.addresses.addrFromAllocId id
      (some ⟨.liveData,true,target.size,target.align,some .other,thread⟩)
      ⟨true,cross,selection,slack⟩) = .ok after) :
    ∃ next, InputDraft.GenerationRepresentation (AddressPost.withAddresses before after) next := by
  obtain ⟨bytes,bytesEq,normalized⟩ := alignment
  obtain ⟨reuseAllowed,crossAllowed,lower,upper⟩ := take_conditions generation.reusePool bucket target.size target.align
    bytes thread cross selection used present bytesEq normalized taken
  have aligned : ∀ row ∈ bucket, row.address % bytes = 0 := by
    have exponent := RawGenerator.normalized_exponent target.align bytes normalized
    have canonical := (RawGenerator.align_metadata target.align exponent).1
    have bytesCanonical : bytes = RawGenerator.alignment target.align := by
      rw [bytesEq] at canonical
      exact Except.ok.inj canonical
    have poolBound := (Array.getElem?_eq_some_iff.mp present).1
    have bucketAt := (Array.getElem?_eq_some_iff.mp present).2
    intro row member
    have alignment := current.poolAlignment target.align.pow2 poolBound row (by simpa only [bucketAt] using member)
    apply UInt64.toNat_inj.mp
    change (row.address % bytes).toNat = 0
    rw [bytesCanonical,UInt64.toNat_mod,RawGenerator.alignment_nat target.align exponent]
    exact alignment
  obtain ⟨proven,next,assignment,post⟩ := AddressPost.reuse_representation before generation current id target thread
    bucket bytes cross selection slack uncached backing live metadata present bytesEq normalized reuseAllowed crossAllowed
    lower upper aligned
  rw [actual] at assignment
  cases assignment
  exact ⟨next,post⟩
end EmptyFunction.ReuseSuccessPost
open Lean in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.ReuseSuccessPost.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved reuse-success axiom {dependency} in {name}"
