import duplicate_prefix.BoolDestinationBorrowCapability
import duplicate_prefix.DuplicatePrefixWriteReadSnapshot
import duplicate_prefix.DuplicatePrefixResidualInitialSnapshot
import duplicate_prefix.DuplicatePrefixReturnPlaceInput

namespace DuplicatePrefix.BoolDestinationWriteOnlyAdapter
open Miri Miri.Memory Miri.ABI Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open GeneralBorrowProjection DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The exact initial Read callback obligation consumed by return protection
follows from the raw Write callback candidate on the SAME state. The existing
cross-kind contributor-list theorem handles differing classifications, including
clamped/absent queries; Read masks are provably empty. No parent-tag/cache order,
Read authorization, future operation result or NoUB premise is introduced.
This relaxes the candidate adapter; necessity of its Write candidate for all
ordinary writable destinations remains a separate coverage question. -/
theorem protector_read_authorization (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (root : UniIndex) (position : Nat)
    (maximum : Option BorTag) (support : UniIndex → Prop)
    (write : Authorization tree location protections root position maximum .Write support)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) :
    Authorization tree location protections root position maximum .Read support := by
  have writeSnapshot := DuplicatePrefixResidualInitialSnapshot.snapshot tree location protections
    root position maximum .Write support write coherent short
  have readSnapshot := DuplicatePrefixWriteReadSnapshot.snapshot tree location protections
    root position maximum support writeSnapshot coherent short write.covers
  exact DuplicatePrefixResidualSupportSnapshotBridge.of_snapshot tree location protections
    root position maximum .Read support readSnapshot write.rooted write.present write.children
    write.covers coherent short (fun removed legal => read_removal_empty tree location protections maximum removed legal)

/-- Write-only exact normal permissions, retaining the same source component.
The existing scalar bridge derives its Read clause rather than requesting it. -/
structure WriteNormal (tree : BorrowTree) (location : LocationTree)
    (protections : ProtectedTags) (source : UniIndex) where
  component : GeneralBorrowExposedScopedNormal.Component
    (source_normal_projection tree default protections).topology source.toNat
  permissions : ∀ index, component.support index → index < tree.nodes.data.size →
    ∃ state, (source_normal_projection tree location protections).stateAt index = some state ∧
      DuplicatePrefixScalarAuthorization.Compatible state .Write
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) source.toNat index)
        ((source_normal_projection tree location protections).protectedNodes.contains index)

/-- Otherwise identical row data, with only initial Write capabilities. This
is a relaxed sufficient adapter packet, NOT a definition of ordinary ownership. -/
structure WriteRow (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag) where
  wildcard : source = none → selectedRoot = none
  rootPath : ∀ anchor, source = some anchor →
    ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast? =
      selectedRoot.map UniIndex.toNat
  rootPresent : ∀ root, selectedRoot = some root → ∃ node, tree.nodeAt root = some node
  cutoff : maximum = selectedRoot.bind (fun root => (tree.nodeAt root).map TreeNode.tag)
  normal : ∀ anchor, source = some anchor → Nonempty (WriteNormal tree location protections anchor)
  callbacks : ∀ position, (valid : position < tree.roots.size) →
    selectedRoot ≠ some tree.roots[position] → ∃ support,
      Authorization tree location protections tree.roots[position] position maximum .Write support

/-- Complete exactly the existing row consumed by protector retagging. -/
theorem WriteRow.complete {tree : BorrowTree} {location : LocationTree} {protections : ProtectedTags}
    {source selectedRoot : Option UniIndex} {maximum : Option BorTag}
    (write : WriteRow tree location protections source selectedRoot maximum)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) :
    DuplicatePrefixBorrowAuthorization.Row tree location protections source selectedRoot maximum := {
  wildcard := write.wildcard
  rootPath := write.rootPath
  rootPresent := write.rootPresent
  cutoff := write.cutoff
  normal := by
    intro anchor selected
    obtain ⟨normal⟩ := write.normal anchor selected
    exact BoolDestinationBorrowCapability.normal_from_writes tree location protections anchor
      normal.component normal.permissions
  callbacks := by
    intro position valid other
    obtain ⟨support, authorization⟩ := write.callbacks position valid other
    exact ⟨support, protector_read_authorization tree location protections _ position maximum support
      authorization coherent short, authorization⟩ }

/-- Same positive window as the existing adapter, requiring Write-only rows.
No initialized bool value is required. Runtime cache coherence and finite-cache
capacity remain separate and are needed only for actual intersecting windows. -/
structure WritePositive (tree : BorrowTree) (protections : ProtectedTags)
    (source selectedRoot : Option UniIndex) (maximum : Option BorTag) (offset len : UInt64) where
  positive : 0 < len.toNat
  bounds : offset.toNat + len.toNat ≤ tree.locations.size.bytes.toNat
  sourcePresent : ∀ anchor, source = some anchor → ∃ node, tree.nodeAt anchor = some node
  wildcardRoot : source = none → 0 < tree.roots.size
  rows : GeneralRangeMapOrigins.OwnedOn
    (fun location => Nonempty (WriteRow tree location protections source selectedRoot maximum))
    offset (offset + len) tree.locations

/-- All relevant byte partitions get their real Read authorization, for both
concrete and wildcard sources and arbitrary selected-root cutoff. -/
theorem WritePositive.complete {tree : BorrowTree} {protections : ProtectedTags}
    {source selectedRoot : Option UniIndex} {maximum : Option BorTag} {offset len : UInt64}
    (write : WritePositive tree protections source selectedRoot maximum offset len)
    (coherent : GeneralRangeMapOrigins.OwnedOn
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
      offset (offset + len) tree.locations)
    (short : tree.nodes.size < 65536) :
    DuplicatePrefixBorrowAuthorization.Positive tree protections source selectedRoot maximum offset len := {
  positive := write.positive
  bounds := write.bounds
  sourcePresent := write.sourcePresent
  wildcardRoot := write.wildcardRoot
  rows := by
    intro position valid nonempty start stop
    obtain ⟨row⟩ := write.rows position valid nonempty start stop
    exact ⟨row.complete (coherent position valid nonempty start stop) short⟩ }

/-- The existing physical bool-place input with its borrow field replaced by
WritePositive, and no other field changed. It is not an ordinary-valid-input
predicate: existing pointer normalization and conservative Write authorization
coverage obligations are retained explicitly. -/
structure WriteInput (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) where
  tracker : MachineHooks.BorrowState
  enabled : before.borrowTracker = some tracker
  pointer : Pointer Provenance
  physicalPointer : place.mplace.ptr = pointer.withOptionalProvenance
  layout : place.layout = RootCompilerFacts.boolLayout
  aligned : place.mplace.misaligned = none
  id : AllocId
  entry : LocalAllocation Provenance BorrowTree MiriMemoryKind
  base : UInt64
  offset : UInt64
  capacity : UInt64
  live : before.memory.live.find? (fun row => row.1 == id) = some (id, entry)
  cachedBase : before.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩
  pointerAddress : pointer.offset.bytes = base + offset
  nonnull : pointer.offset.bytes ≠ 0
  addressFits : base.toNat + capacity.toNat < 2^64
  bounds : offset.toNat + 1 ≤ capacity.toNat
  size : entry.allocation.byteSize = Size.ofBytes capacity
  bytes : entry.allocation.len = capacity.toNat
  mutable : entry.allocation.mutability = .Mut
  maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask
  maskLength : entry.allocation.initializationMask.len = Size.ofBytes capacity
  provenanceMap : ProvenanceCopy.WellFormed entry.allocation.provenanceMap entry.allocation.len
  borrowSize : entry.allocation.extra.locations.size.bytes = capacity
  source : Option UniIndex
  selectedRoot : Option UniIndex
  maximum : Option BorTag
  binding : DuplicatePrefixReferenceInput.Binding before.user.addresses pointer id base
    entry.allocation.byteSize entry.allocation.extra source
  borrow : WritePositive entry.allocation.extra tracker.global.protectedTags
    source selectedRoot maximum offset 1

/-- Existing destination-entry proofs accept this completed input directly.
Only initial Write capabilities were supplied; the protector Read data is
constructed for every overlapping physical row. No execution result is assumed. -/
def WriteInput.complete {before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser}
    {place : MPlaceTy Provenance} (write : WriteInput before place)
    (coherent : GeneralRangeMapOrigins.OwnedOn
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent
        write.entry.allocation.extra location write.tracker.global.protectedTags)
      write.offset (write.offset + 1) write.entry.allocation.extra.locations)
    (short : write.entry.allocation.extra.nodes.size < 65536) :
    DuplicatePrefixReturnPlaceInput.Input before place := {
  tracker := write.tracker
  enabled := write.enabled
  pointer := write.pointer
  physicalPointer := write.physicalPointer
  layout := write.layout
  aligned := write.aligned
  id := write.id
  entry := write.entry
  base := write.base
  offset := write.offset
  capacity := write.capacity
  live := write.live
  cachedBase := write.cachedBase
  pointerAddress := write.pointerAddress
  nonnull := write.nonnull
  addressFits := write.addressFits
  bounds := write.bounds
  size := write.size
  bytes := write.bytes
  mutable := write.mutable
  maskValid := write.maskValid
  maskLength := write.maskLength
  provenanceMap := write.provenanceMap
  borrowSize := write.borrowSize
  source := write.source
  selectedRoot := write.selectedRoot
  maximum := write.maximum
  binding := write.binding
  borrow := write.borrow.complete coherent short }

end DuplicatePrefix.BoolDestinationWriteOnlyAdapter
