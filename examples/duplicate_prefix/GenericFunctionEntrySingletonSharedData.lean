import duplicate_prefix.GenericFunctionEntrySingleton
import duplicate_prefix.GenericFunctionEntryMetadata
import duplicate_prefix.GenericFunctionEntryClean
import duplicate_prefix.GenericFunctionEntryFreshness
import duplicate_prefix.GeneralBorrowFreshSharedNext
namespace DuplicatePrefix.GenericFunctionEntrySingletonSharedData
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
/-- An append shared-child input from the already-derived actual ROOT metadata.
The allocator, cleanliness and freshness are structural data; the singleton
entry point below derives them from the original tree. -/
noncomputable def append_from_metadata (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len≠0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (metadata : GenericFunctionEntryMetadata.Output tree tracker parentTag offset len data)
    (noFree : (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).tagMapping.deassigned.back?=none)
    (aligned : (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).tagMapping.mapping.size=
      (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).nodes.data.size)
    (fits : (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).tagMapping.mapping.size≤4294967295)
    (clean : GeneralBorrowFreshFutureClean.Clean (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len)
      ⟨UInt32.ofNat (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).tagMapping.mapping.size⟩)
    (newTag : BorTag)
    (mapFresh : GeneralBorrowTagMap.Fresh (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).tagMapping newTag)
    (nodeFresh : GeneralBorrowProtector.Fresh (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len) newTag) :
    GeneralBorrowFreshSharedSequence.Data (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len) newTag
      (GeneralBorrowFreshMutableStages.slot_index data.slot) offset len := by
  let node := Classical.choose metadata.node
  have present := Classical.choose_spec metadata.node
  exact ⟨tracker.global.nextPointerTag,data.root,node,metadata.certificates.depth,metadata.certificates.children,
    present.1,metadata.roots,metadata.certificates.covered,metadata.lookup,mapFresh,nodeFresh,metadata.nodeFits,
    .append noFree aligned fits,nonzero,metadata.well,(by rw [metadata.capacity];exact bounds),clean⟩

set_option autoImplicit false in
/-- The one initial reuse lies below the initial node bound. Every later append
query starts at or beyond that bound; vacancy/distinctness are derived. -/
theorem later_clean (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len≠0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (q : UniIndex) (singleton : tree.tagMapping.deassigned=#[q])
    (balanced : tree.tagMapping.mapping.size+1=tree.nodes.data.size)
    (step : Nat) (positive : 0<step) (fits : tree.tagMapping.mapping.size+step<4294967296)
    (clean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+step)⟩) :
    let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    let query : UniIndex := ⟨UInt32.ofNat (tree.tagMapping.mapping.size+step)⟩
    after.nodes.get query=none ∧ GeneralBorrowFreshFutureClean.Clean after query := by
  let query : UniIndex := ⟨UInt32.ofNat (tree.tagMapping.mapping.size+step)⟩
  have queryNat : query.toNat=tree.tagMapping.mapping.size+step := by
    simp only [query,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt fits]
  obtain ⟨ready,selected,bound⟩ := GenericFunctionEntrySingleton.allocator tree tracker parentTag offset len nonzero data bounds q singleton balanced
  have vacant : tree.nodes.get query=none := by
    unfold UniValMap.get
    simp only [queryNat,Array.getElem?_eq_none (by omega : tree.nodes.data.size≤tree.tagMapping.mapping.size+step)]
  have different : query≠GeneralBorrowFreshMutableStages.slot_index data.slot := by
    intro same
    have equal := congrArg UniIndex.toNat same
    rw [queryNat,selected] at equal
    omega
  exact GenericFunctionEntryClean.future tree tracker parentTag offset len nonzero data bounds query vacant different clean

set_option autoImplicit false in
/-- A singleton reuse leaves the next two shared append slots clean. -/
theorem two_clean (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len≠0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (q : UniIndex) (singleton : tree.tagMapping.deassigned=#[q])
    (balanced : tree.tagMapping.mapping.size+1=tree.nodes.data.size) (room : tree.tagMapping.mapping.size+2≤4294967295)
    (firstClean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩)
    (secondClean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+2)⟩) :
    let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    GeneralBorrowFreshFutureClean.Clean after ⟨UInt32.ofNat after.tagMapping.mapping.size⟩ ∧
      GeneralBorrowFreshFutureClean.Clean after (GeneralBorrowFreshSharedNext.future after) := by
  have allocator := (GenericFunctionEntrySingleton.allocator tree tracker parentTag offset len nonzero data bounds q singleton balanced).1
  have first := (later_clean tree tracker parentTag offset len nonzero data bounds q singleton balanced 1 (by omega) (by omega) firstClean).2
  have second := (later_clean tree tracker parentTag offset len nonzero data bounds q singleton balanced 2 (by omega) (by omega) secondClean).2
  simpa only [allocator.mappingSize,GeneralBorrowFreshSharedNext.future,Nat.add_assoc] using And.intro first second

set_option autoImplicit false in
/-- The real singleton ROOT FnEntry is followed by an ordinary append shared
expression. All allocator, metadata and future-slot facts are derived. -/
noncomputable def first (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag)
    (offset len : UInt64) (nonzero : len≠0)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (bounds : offset.toNat+len.toNat≤tree.locations.size.bytes.toNat)
    (q : UniIndex) (singleton : tree.tagMapping.deassigned=#[q])
    (balanced : tree.tagMapping.mapping.size+1=tree.nodes.data.size) (room : tree.tagMapping.mapping.size+2≤4294967295)
    (firstClean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩)
    (newTag : BorTag) (mapFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (nodeFresh : GeneralBorrowProtector.Fresh tree newTag) (different : tracker.global.nextPointerTag≠newTag) :
    GeneralBorrowFreshSharedSequence.Data (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len) newTag
      (GeneralBorrowFreshMutableStages.slot_index data.slot) offset len := by
  let metadata := GenericFunctionEntryMetadata.build tree tracker parentTag offset len nonzero data bounds
  have allocator := (GenericFunctionEntrySingleton.allocator tree tracker parentTag offset len nonzero data bounds q singleton balanced).1
  have freshness := GenericFunctionEntryFreshness.future tree tracker parentTag offset len nonzero data bounds newTag nodeFresh different
  have clean := (later_clean tree tracker parentTag offset len nonzero data bounds q singleton balanced 1 (by omega) (by omega) firstClean).2
  have newClean : GeneralBorrowFreshFutureClean.Clean (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len)
      ⟨UInt32.ofNat (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len).tagMapping.mapping.size⟩ := by
    rw [allocator.mappingSize]
    exact clean
  exact append_from_metadata tree tracker parentTag offset len nonzero data bounds metadata
    (by rw [allocator.empty];rfl) allocator.aligned (by rw [allocator.mappingSize];omega) newClean newTag (freshness.1 mapFresh) freshness.2

end DuplicatePrefix.GenericFunctionEntrySingletonSharedData
