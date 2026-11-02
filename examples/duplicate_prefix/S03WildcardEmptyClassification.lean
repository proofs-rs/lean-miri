import duplicate_prefix.S05ConsistentCallSpecification

namespace DuplicatePrefix.S03WildcardEmptyClassification
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixEmptyReferenceInput DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Raw selected wildcard hit, with current address/metadata facts rather
than a pointer-resolution or retag success premise. -/
structure Hit {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64) where
  id : AllocId
  base : UInt64
  info : AllocationInfo
  known : memory.getAllocInfo id = .ok info
  geometry : WildcardGeneralHitReborrow.Geometry addresses.intToPtrMap address base id info.size
  exposed : addresses.exposed.contains id = true
  cached : addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩
  target : TargetMetadata context memory addresses id none

/-- Candidate's coherent inverse map supplies the actual miss/hit dispatch.
No selected resolver result or successful retag is a hypothesis. -/
theorem classify {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64)
    (input : Wildcard context memory addresses) :
    addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup memory) = .ok none ∨
      Nonempty (Hit context memory addresses address) := by
  rcases WildcardEmptyCoherentResolution.classify memory addresses address input.coherent input.nonstrict input.sizes with
    ⟨position,row,valid,present,equal,done⟩ | ⟨cut,partition,choice⟩
  · by_cases exposed : addresses.exposed.contains row.allocId = true
    · have member := Array.mem_of_getElem? present
      have target := input.targets row member exposed
      obtain ⟨info,known⟩ := target_metadata_known context memory addresses row.allocId none target
      exact Or.inr ⟨⟨row.allocId,row.address,info,known,Or.inl ⟨equal.symm,position,valid,input.coherent.ordered,present⟩,
        exposed,input.cached row member exposed,target⟩⟩
    · change addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup memory) =
        .ok (if addresses.exposed.contains row.allocId = true then some row.allocId else none) at done
      rw [if_neg exposed] at done
      exact Or.inl done
  · rcases choice with ⟨zero,done⟩ | ⟨row,info,nonzero,present,known,nondead,done⟩
    · exact Or.inl done
    · by_cases inside : address-row.address < info.size.bytes ∧ addresses.exposed.contains row.allocId = true
      · have member := Array.mem_of_getElem? present
        have position : cut-1+1 = cut := by omega
        have target := input.targets row member inside.2
        exact Or.inr ⟨⟨row.allocId,row.address,info,known,
          Or.inr ⟨cut-1,by rw [position];exact partition,present,inside.1⟩,
          inside.2,input.cached row member inside.2,target⟩⟩
      · rw [if_neg inside] at done
        exact Or.inl done

/-- The original contract supplies the raw coherent wildcard candidate. -/
theorem candidate {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : Contract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard) :
    pointer.offset.bytes ≠ 0 ∧ Wildcard (imageContext options before input.tracker) before.memory before.user.addresses := by
  have raw : Candidate (imageContext options before input.tracker) before.memory before.user.addresses pointer.withOptionalProvenance := by
    cases reference : input.reference with
    | empty zero metadata => exact metadata
    | positive value encoding positive => have bad := positive.borrow.positive;contradiction
  simpa only [Candidate,Pointer.withOptionalProvenance,wildcard] using raw

/-- The actual wildcard domain reaches one of the source lookup alternatives,
rather than requiring a caller to select a successful invocation family. -/
theorem contract {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {pointer : Pointer Provenance} {place : MPlaceTy Provenance}
    (input : Contract options limits remaining span before (.pointer pointer) 0 place)
    (wildcard : pointer.provenance = .wildcard) :
    before.user.addresses.allocIdFromAddr pointer.offset.bytes 0 (GlobalAddressLiveErrorExclusion.lookup before.memory) = .ok none ∨
      Nonempty (Hit (imageContext options before input.tracker) before.memory before.user.addresses pointer.offset.bytes) :=
  classify _ _ _ _ (candidate input wildcard).2

end
end DuplicatePrefix.S03WildcardEmptyClassification
