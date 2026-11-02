import duplicate_prefix.GenericFunctionEntryAppend
import duplicate_prefix.GeneralBorrowFreshSharedNext

namespace DuplicatePrefix.GenericFunctionEntrySharedData
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
theorem later_clean (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (step : Nat) (positive : 0 < step) (fits : tree.tagMapping.mapping.size+step < 4294967296)
    (clean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+step)⟩) :
    let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    let query : UniIndex := ⟨UInt32.ofNat (tree.tagMapping.mapping.size+step)⟩
    after.nodes.get query = none ∧ GeneralBorrowFreshFutureClean.Clean after query := by
  let query : UniIndex := ⟨UInt32.ofNat (tree.tagMapping.mapping.size+step)⟩
  have queryNat : query.toNat = tree.tagMapping.mapping.size+step := by
    simp only [query,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt fits]
  have aligned : tree.tagMapping.mapping.size = tree.nodes.data.size := by
    cases data.slot with
    | append empty aligned fits => exact aligned
    | reuse index available valid vacant slack => rw [noFree] at available;cases available
  have indexNat : (GeneralBorrowFreshMutableStages.slot_index data.slot).toNat = tree.tagMapping.mapping.size := by
    cases data.slot with
    | append empty aligned fitsIndex =>
      simp only [GeneralBorrowFreshMutableStages.slot_index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 4294967296)]
    | reuse index available valid vacant slack => rw [noFree] at available;cases available
  have vacant : tree.nodes.get query = none := by
    unfold UniValMap.get
    simp only [queryNat,Array.getElem?_eq_none (by omega : tree.nodes.data.size ≤ tree.tagMapping.mapping.size+step)]
  have different : query ≠ GeneralBorrowFreshMutableStages.slot_index data.slot := by
    intro same
    have eq := congrArg UniIndex.toNat same
    rw [queryNat,indexNat] at eq
    omega
  exact GenericFunctionEntryClean.future tree tracker parentTag offset len nonzero data bounds query vacant different clean

set_option autoImplicit false in
/-- Both subsequent append slots are prepared from their INITIAL absence of
permissions; vacancy and distinctness are derived from allocator arithmetic. -/
theorem two_clean (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (noFree : tree.tagMapping.deassigned.back? = none) (room : tree.tagMapping.mapping.size+2 ≤ 4294967295)
    (firstClean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩)
    (secondClean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+2)⟩) :
    let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    GeneralBorrowFreshFutureClean.Clean after ⟨UInt32.ofNat after.tagMapping.mapping.size⟩ ∧
      GeneralBorrowFreshFutureClean.Clean after (GeneralBorrowFreshSharedNext.future after) := by
  have allocator := GenericFunctionEntryAppend.allocator tree tracker parentTag offset len nonzero data bounds noFree
  have first := (later_clean tree tracker parentTag offset len nonzero data bounds noFree 1 (by omega) (by omega) firstClean).2
  have second := (later_clean tree tracker parentTag offset len nonzero data bounds noFree 2 (by omega) (by omega) secondClean).2
  simpa only [allocator.2.2.2,GeneralBorrowFreshSharedNext.future,Nat.add_assoc] using And.intro first second

set_option autoImplicit false in
/-- Form the shared-expression input record internally from the ORIGINAL mutable
caller data and initial future tag/slot freshness. -/
noncomputable def first (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (noFree : tree.tagMapping.deassigned.back? = none) (room : tree.tagMapping.mapping.size+2 ≤ 4294967295)
    (firstClean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩)
    (newTag : BorTag) (mapFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (nodeFresh : GeneralBorrowProtector.Fresh tree newTag) (different : tracker.global.nextPointerTag ≠ newTag) :
    GeneralBorrowFreshSharedSequence.Data (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len) newTag
      (GeneralBorrowFreshMutableStages.slot_index data.slot) offset len := by
  classical
  let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
  let metadata := GenericFunctionEntryMetadata.build tree tracker parentTag offset len nonzero data bounds
  have allocator := GenericFunctionEntryAppend.allocator tree tracker parentTag offset len nonzero data bounds noFree
  have freshness := GenericFunctionEntryFreshness.future tree tracker parentTag offset len nonzero data bounds newTag nodeFresh different
  let node := Classical.choose metadata.node
  have present := Classical.choose_spec metadata.node
  have fits : after.tagMapping.mapping.size ≤ 4294967295 := by rw [allocator.2.2.2];omega
  let slot : GeneralBorrowFreshReborrowStages.Slot after metadata.certificates.depth
      (GeneralBorrowFreshMutableStages.slot_index data.slot) :=
    GeneralBorrowFreshReborrowStages.Slot.append allocator.1 allocator.2.1 fits
  have clean := (later_clean tree tracker parentTag offset len nonzero data bounds noFree 1 (by omega) (by omega) firstClean).2
  have newClean : GeneralBorrowFreshFutureClean.Clean after ⟨UInt32.ofNat after.tagMapping.mapping.size⟩ := by
    dsimp only [after]
    rw [allocator.2.2.2]
    exact clean
  exact ⟨tracker.global.nextPointerTag,data.root,node,metadata.certificates.depth,metadata.certificates.children,
    present.1,metadata.roots,metadata.certificates.covered,metadata.lookup,freshness.1 mapFresh,freshness.2,
    metadata.nodeFits,slot,nonzero,metadata.well,(by rw [metadata.capacity];exact bounds),newClean⟩

end DuplicatePrefix.GenericFunctionEntrySharedData
