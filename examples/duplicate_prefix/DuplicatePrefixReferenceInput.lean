import duplicate_prefix.DuplicatePrefixBorrowAuthorization
import duplicate_prefix.DuplicatePrefixSliceStorage
import duplicate_prefix.WildcardGeneralHitReborrow
import duplicate_prefix.ProvenanceCopy

namespace DuplicatePrefix.DuplicatePrefixReferenceInput
open Miri Miri.Memory Miri.ABI Miri.TreeBorrows Miri.Interpreter

set_option autoImplicit false in
/-- Concrete/wildcard provenance binding to the actual live allocation and
borrow source. Wildcard geometry is the raw finite inverse-map base/interior
predicate, not assumed successful resolution. This normalized interface still
requires an existing base-address row; its coverage is a caller/runtime bridge
obligation, not a premise silently called ordinary reference validity. -/
def Binding (addresses : Miri.Memory.AllocAddresses.GlobalAddressState)
    (pointer : Pointer Provenance) (id : AllocId) (base : UInt64) (size : Size)
    (tree : BorrowTree) (source : Option UniIndex) : Prop :=
  match pointer.provenance with
  | .concrete supplied tag => supplied = id ∧ ∃ anchor,
      source = some anchor ∧ tree.indexOfTag tag = some anchor
  | .wildcard => source = none ∧ addresses.provenanceMode ≠ .strict ∧
      addresses.exposed.contains id = true ∧
      WildcardGeneralHitReborrow.Geometry addresses.intToPtrMap pointer.offset.bytes base id size

set_option autoImplicit false in
/-- A normalized positive-reference CANDIDATE combining physical backing,
count-independent u8 storage, provenance binding and the raw borrow-capability
candidate. It assumes no operation result, target trace or final profile.
Its conservative authorization and address-row normalization still need a
valid-input coverage bridge; defining this record does not supply that bridge.
No restriction is placed on unrelated allocations or outside-window rights. -/
structure Positive {K U : Type} (before : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (pointer : Pointer Provenance) (len : UInt64) where
  tracker : MachineHooks.BorrowState
  enabled : before.borrowTracker = some tracker
  id : AllocId
  entry : LocalAllocation Provenance BorrowTree K
  base : UInt64
  offset : UInt64
  capacity : UInt64
  live : before.memory.live.find? (fun row => row.1 == id) = some (id, entry)
  cachedBase : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩
  pointerAddress : pointer.offset.bytes = base + offset
  nonnull : pointer.offset.bytes ≠ 0
  addressFits : base.toNat + capacity.toNat < 2^64
  size : entry.allocation.byteSize = Size.ofBytes capacity
  bytes : entry.allocation.len = capacity.toNat
  mutable : entry.allocation.mutability = .Mut
  storage : DuplicatePrefixSliceStorage.Positive entry.allocation.initializationMask capacity offset len
  provenanceMap : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  borrowSize : entry.allocation.extra.locations.size.bytes = capacity
  source : Option UniIndex
  selectedRoot : Option UniIndex
  maximum : Option BorTag
  binding : Binding before.user.addresses pointer id base entry.allocation.byteSize entry.allocation.extra source
  borrow : DuplicatePrefixBorrowAuthorization.Positive entry.allocation.extra tracker.global.protectedTags
    source selectedRoot maximum offset len

end DuplicatePrefix.DuplicatePrefixReferenceInput
