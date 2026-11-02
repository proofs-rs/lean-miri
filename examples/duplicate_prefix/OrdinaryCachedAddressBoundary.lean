import duplicate_prefix.OrdinaryLiveInverseFormation
import duplicate_prefix.OrdinaryDistinctAddressBoundary
namespace DuplicatePrefix.OrdinaryCachedAddressBoundary
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
noncomputable section
/-- The global reverse-cache representation relation supplies inverse rows
for distinct, nonzero cached live allocations. Existing extent geometry then
derives both addressFits fields and the exact Contract.separated disjunction.
No selected inverse index or successful operation is assumed. Zero bases,
formation of arbitrary current states and complete ordinary validity are not
certified by this conditional representation bridge. -/
theorem separated {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (sizes : AllocId → Size)
    (representation : GlobalAddressReuseManagedResources.Post memory addresses sizes)
    (inverse : OrdinaryLiveInverseFormation.LiveInverse memory addresses)
    (sourceId destinationId : AllocId)
    (sourceEntry destinationEntry : LocalAllocation Provenance BorrowTree K)
    (sourceLive : memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry))
    (destinationLive : memory.live.find? (fun row => row.1 == destinationId) = some (destinationId,destinationEntry))
    (different : sourceId ≠ destinationId)
    (sourceBase sourceOffset len sourceAddress destinationBase destinationOffset destinationAddress : UInt64)
    (sourceNonzero : sourceBase ≠ 0) (destinationNonzero : destinationBase ≠ 0)
    (sourceCache : addresses.baseAddr.find? (fun row => row.allocId == sourceId) = some ⟨sourceId,sourceBase⟩)
    (destinationCache : addresses.baseAddr.find? (fun row => row.allocId == destinationId) = some ⟨destinationId,destinationBase⟩)
    (sourcePhysical : OrdinaryPhysicalValidity.MutU8Slice sourceEntry.allocation sourceOffset len)
    (destinationPhysical : OrdinaryPhysicalValidity.BoolDestination destinationEntry.allocation destinationOffset)
    (sourceBinding : sourceAddress = sourceBase+sourceOffset)
    (destinationBinding : destinationAddress = destinationBase+destinationOffset) :
    sourceBase.toNat+sourceEntry.allocation.byteSize.bytes.toNat < 2^64 ∧
    destinationBase.toNat+destinationEntry.allocation.byteSize.bytes.toNat < 2^64 ∧
    (len = 0 ∨ sourceAddress.toNat+len.toNat ≤ destinationAddress.toNat ∨
      destinationAddress.toNat+1 ≤ sourceAddress.toNat) := by
  have sourceMember := inverse ⟨sourceId,sourceBase⟩ (Array.mem_of_find?_eq_some sourceCache) sourceNonzero ⟨sourceEntry,sourceLive⟩
  have destinationMember := inverse ⟨destinationId,destinationBase⟩ (Array.mem_of_find?_eq_some destinationCache) destinationNonzero ⟨destinationEntry,destinationLive⟩
  exact OrdinaryDistinctAddressBoundary.registered_rows memory addresses sizes representation sourceId destinationId sourceEntry destinationEntry sourceLive destinationLive different
    sourceBase sourceOffset len sourceAddress destinationBase destinationOffset destinationAddress sourceMember destinationMember
    sourcePhysical destinationPhysical sourceBinding destinationBinding
end
end DuplicatePrefix.OrdinaryCachedAddressBoundary
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.OrdinaryCachedAddressBoundary.separated) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved cached address boundary dependency {dependency}"
