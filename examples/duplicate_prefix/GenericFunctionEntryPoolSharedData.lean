import duplicate_prefix.GenericFunctionEntryPool
import duplicate_prefix.GenericFunctionEntryClean
import duplicate_prefix.GeneralBorrowTightAncestry

namespace DuplicatePrefix.GenericFunctionEntryPoolSharedData
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshAllocatorInvariant GeneralBorrowFreshStagePool
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
/-- Every remaining vacant slot is initially vacant and clean. The actual ROOT
child occupies its chosen slot, so permission-clean transport uses a different slot. -/
theorem vacant_clean (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (pool : Pool tree.nodes tree.tagMapping.deassigned) (accounting : Accounting tree)
    (cleanVacant : ∀ query, tree.nodes.get query = none → GeneralBorrowFreshFutureClean.Clean tree query)
    (query : UniIndex)
    (vacant : (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).nodes.get query = none) :
    tree.nodes.get query = none ∧
      GeneralBorrowFreshFutureClean.Clean (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len) query := by
  have allocator := GenericFunctionEntryPool.allocator tree tracker parentTag offset len nonzero data bounds pool accounting
  have initiallyVacant : tree.nodes.get query = none := by
    cases initial : tree.nodes.get query with
    | none => rfl
    | some old =>
      obtain ⟨next,lookup,_,_⟩ := allocator.2.2.2 query old initial
      change (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).nodes.get query = some next at lookup
      rw [vacant] at lookup
      cases lookup
  have metadata := GenericFunctionEntryMetadata.build tree tracker parentTag offset len nonzero data bounds
  have different : query ≠ GeneralBorrowFreshMutableStages.slot_index data.slot := by
    intro same
    obtain ⟨node,present,_,_⟩ := metadata.node
    change (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).nodes.get _ = some node at present
    rw [←same,vacant] at present
    cases present
  exact ⟨initiallyVacant,(GenericFunctionEntryClean.future tree tracker parentTag offset len nonzero data bounds
    query initiallyVacant different (cleanVacant query initiallyVacant)).2⟩

set_option autoImplicit false in
/-- The first shared input after the real ROOT FnEntry, for an arbitrary coherent
free pool. Initial vacancy cleanliness is explicit and is not inferred from
node vacancy. The conservative node room bound covers append and reuse. -/
noncomputable def first (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (pool : Pool tree.nodes tree.tagMapping.deassigned) (accounting : Accounting tree)
    (room : tree.nodes.size+1 ≤ 4294967295)
    (cleanVacant : ∀ query, tree.nodes.get query = none → GeneralBorrowFreshFutureClean.Clean tree query)
    (newTag : BorTag) (mapFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (nodeFresh : GeneralBorrowProtector.Fresh tree newTag) (different : tracker.global.nextPointerTag ≠ newTag) :
    {first : GeneralBorrowFreshSharedSequence.Data (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len)
        newTag (GeneralBorrowFreshMutableStages.slot_index data.slot) offset len //
      first.parentTag = tracker.global.nextPointerTag ∧ first.parentNode.isExposed = false ∧
      tree.nodes.get (GeneralBorrowFreshSharedSequence.index first) = none ∧
      GeneralBorrowFreshSharedSequence.index first ≠ GeneralBorrowFreshMutableStages.slot_index data.slot} := by
  let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
  have metadata := GenericFunctionEntryMetadata.build tree tracker parentTag offset len nonzero data bounds
  have allocator := GenericFunctionEntryPool.allocator tree tracker parentTag offset len nonzero data bounds pool accounting
  let node := Classical.choose metadata.node
  have nodeFacts := Classical.choose_spec metadata.node
  have present : after.nodes.get (GeneralBorrowFreshMutableStages.slot_index data.slot) = some node := nodeFacts.1
  let depth := GeneralBorrowTightAncestry.tight after.nodes metadata.certificates.depth
  have slack : depth.depth (GeneralBorrowFreshMutableStages.slot_index data.slot) < after.nodes.size :=
    GeneralBorrowTightAncestry.present_slack after.nodes metadata.certificates.depth _ node present
  have fits : after.tagMapping.mapping.size ≤ 4294967295 := by
    have accounted := allocator.2.1
    change Accounting after at accounted
    unfold Accounting at accounted
    have sizeBound := allocator.2.2.1
    change after.nodes.size ≤ tree.nodes.size+1 at sizeBound
    omega
  let slot := GeneralBorrowFreshAllocatorInvariant.slot after depth (GeneralBorrowFreshMutableStages.slot_index data.slot)
    allocator.1 (empty_aligned after allocator.2.1) (fun _ => fits) slack
  let query := GeneralBorrowFreshSharedWithinStages.slot_index slot
  have vacant : after.nodes.get query = none := GeneralBorrowFreshSharedWithinStages.slot_vacant after depth _ slot
  have cleaned := vacant_clean tree tracker parentTag offset len nonzero data bounds pool accounting cleanVacant query vacant
  have nextDifferent : query ≠ GeneralBorrowFreshMutableStages.slot_index data.slot := by
    intro same
    rw [same,present] at vacant
    cases vacant
  have freshness := GenericFunctionEntryFreshness.future tree tracker parentTag offset len nonzero data bounds newTag nodeFresh different
  let first : GeneralBorrowFreshSharedSequence.Data after newTag (GeneralBorrowFreshMutableStages.slot_index data.slot) offset len := {
    parentTag := tracker.global.nextPointerTag, root := data.root, parentNode := node, depth := depth
    children := metadata.certificates.children, parentPresent := present, roots := metadata.roots
    covered := metadata.certificates.covered, parentTagPresent := metadata.lookup
    tagFresh := freshness.1 mapFresh, protectorFresh := freshness.2, nodeFits := metadata.nodeFits
    slot := slot, nonzero := nonzero, well := metadata.well
    bounds := by rw [metadata.capacity];exact bounds
    clean := cleaned.2 }
  exact ⟨first,rfl,nodeFacts.2.2,cleaned.1,nextDifferent⟩

end DuplicatePrefix.GenericFunctionEntryPoolSharedData
