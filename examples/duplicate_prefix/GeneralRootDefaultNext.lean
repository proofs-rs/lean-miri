import duplicate_prefix.GeneralRootDefaultMetadataCore
import duplicate_prefix.GenericAsMutPtrEntryValidity
import duplicate_prefix.GeneralBorrowFreshActiveOnRange
import duplicate_prefix.GeneralBorrowFreshMutableStages
namespace DuplicatePrefix.GeneralRootDefaultNext
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshReadFrame DuplicatePrefix.GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option autoImplicit false in
/-- Form the next protected mutable FnEntry's tree contract from initial
unprotected-expression data. Both allocator steps use explicit append scope. -/
noncomputable def build (tree : BorrowTree) (newTag nextTag : BorTag) (parent : UniIndex) (protections : ProtectedTags)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (data : GeneralBorrowFreshDefaultSequence.Data tree newTag parent offset len)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write) offset (offset+len) tree.locations)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree parent .Write offset (offset+len))
    (noFree : tree.tagMapping.deassigned.back? = none)
    (room : tree.tagMapping.mapping.size+1 ≤ 4294967295)
    (nextFresh : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag)
    (nextNodeFresh : GeneralBorrowProtector.Fresh tree nextTag) (differentTag : newTag ≠ nextTag)
    (futureClean : GeneralBorrowFreshFutureClean.Clean tree ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩) :
    let after := (GeneralBorrowFreshDefaultSequence.child data protections).tree
    Σ' next : GenericAsMutPtrEntryValidity.Data after protections newTag nextTag offset len,
      GeneralBorrowFreshFutureClean.Clean after (GeneralBorrowFreshMutableStages.slot_index next.slot) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin after parent .Write offset (offset+len) := by
  classical
  let registered := protections
  let accessed := tree.performBorrowAccessRange (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have owners := owned
  have good := GeneralBorrowRangeLocal.access tree registered data.parentTag parent data.root (Size.ofBytes offset) (Size.ofBytes len)
    .Read .Write .VisitChildrenOfAccessed (fun _ => rfl) data.nodeFits data.depth data.children data.parentNode data.parentPresent
    data.roots data.covered data.parentTagPresent data.well offset (offset+len) owners bounds (Nat.le_refl _) (Nat.le_refl _)
  change accessed.status = .Completed ∧ GeneralRangeMapOrigins.OwnedOn
    (GeneralBorrowRange.LocationOwned accessed.tree registered parent .Write) offset (offset+len) accessed.tree.locations ∧
    accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  change accessed.tree = {tree with locations := accessed.tree.locations} at framed
  have nodes : accessed.tree.nodes = tree.nodes := by
    have equality := congrArg BorrowTree.nodes framed
    exact equality
  have mapping : accessed.tree.tagMapping = tree.tagMapping := by
    have equality := congrArg BorrowTree.tagMapping framed
    exact equality
  have roots : accessed.tree.roots = tree.roots := by
    have equality := congrArg BorrowTree.roots framed
    exact equality
  let depth := depth_on tree accessed.tree nodes data.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [framed];exact data.children
  have covered : GeneralBorrowGraph.RootsCover accessed.tree := by rw [framed];exact data.covered
  have parentPresent : accessed.tree.nodeAt parent = some data.parentNode := by
    change accessed.tree.nodes.get parent = _;rw [nodes];exact data.parentPresent
  have tagPresent : accessed.tree.tagMapping.get data.parentTag = some parent := by rw [mapping];exact data.parentTagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact data.tagFresh
  have fits : accessed.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact data.nodeFits
  have bounded : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact bounds
  let slot := GeneralBorrowFreshMetadataChildDefaultSlot.transport tree accessed.tree data.depth depth nodes mapping rfl parent data.slot
  have indexEq : GeneralBorrowFreshMetadataChildDefaultSlot.index slot = GeneralBorrowFreshDefaultSequence.index data := by
    exact (GeneralBorrowFreshMetadataChildDefaultSlot.transport_index tree accessed.tree data.depth depth nodes mapping rfl parent data.slot).trans
      (by unfold GeneralBorrowFreshDefaultSequence.index;cases data.slot <;> rfl)
  have metadata := GeneralBorrowFreshMetadataChildDefaultSlot.build accessed.tree depth children covered data.parentTag newTag
    parent data.parentNode tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 fits bounded
  have sameTree : GeneralBorrowFreshMetadataChildDefaultSlot.result accessed.tree data.parentTag newTag offset len =
      (GeneralBorrowFreshDefaultSequence.child data protections).tree := rfl
  have initialAligned : tree.tagMapping.mapping.size = tree.nodes.data.size := by
    cases data.slot with
    | append empty aligned fits => exact aligned
    | reuse q available bounded vacant slack => rw [noFree] at available; cases available
  have empty : accessed.tree.tagMapping.deassigned.back? = none := by rw [mapping];exact noFree
  have aligned : accessed.tree.tagMapping.mapping.size = accessed.tree.nodes.data.size := by rw [mapping,nodes];exact initialAligned
  have appendFits : accessed.tree.tagMapping.mapping.size ≤ 4294967295 := by rw [mapping];omega
  let input : GeneralBorrowFreshMetadataChildDefault.Input :=
    ⟨accessed.tree,depth,children,covered,data.parentTag,newTag,parent,data.parentNode,tagPresent,parentPresent,fresh,
      empty,aligned,appendFits,offset,len,nonzero,good.2.2.1,bounded⟩
  let added := GeneralBorrowFreshMetadataChildDefault.append input
  let after := (GeneralBorrowFreshDefaultSequence.child data protections).tree
  have resultEq : GeneralBorrowFreshMetadataChildDefault.result input = after := rfl
  have pool : after.tagMapping.deassigned.back? = none := added.noFree
  have mapSize : after.tagMapping.mapping.size = tree.tagMapping.mapping.size+1 := by
    change (GeneralBorrowFreshMetadataChildDefault.result input).tagMapping.mapping.size = _
    rw [added.mapping]
    simp only [GeneralBorrowFreshMetadataChildDefault.mapping,Array.size_push,input,mapping]
  have afterAligned : after.tagMapping.mapping.size = after.nodes.data.size := added.aligned
  have afterFits : after.tagMapping.mapping.size ≤ 4294967295 := by rw [mapSize];exact room
  let nextSlot : Slot after metadata.certificates.depth (GeneralBorrowFreshDefaultSequence.index data) :=
    Slot.append pool afterAligned afterFits
  have freshNext : GeneralBorrowTagMap.Fresh after.tagMapping nextTag := by
    change GeneralBorrowTagMap.Fresh (GeneralBorrowFreshMetadataChildDefault.result input).tagMapping nextTag
    rw [added.mapping]
    exact GeneralBorrowFreshMetadataChildAllocator.fresh_push _ _ _ _ _ (by rw [mapping];exact nextFresh) differentTag
  have nodeFreshNext : GeneralBorrowProtector.Fresh after nextTag := by
    exact (GeneralRootDefaultFreshSlot.mutable_slot accessed.tree depth children covered data.parentTag newTag parent data.parentNode
      tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 bounded nextTag
      (by rw [framed];exact nextNodeFresh) differentTag).2
  let query : UniIndex := ⟨UInt32.ofNat (tree.tagMapping.mapping.size+1)⟩
  have queryNat : query.toNat = tree.tagMapping.mapping.size+1 := by
    simp only [query,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size+1 < 4294967296)]
  have vacant : tree.nodes.get query = none := by
    unfold UniValMap.get
    rw [Array.getElem?_eq_none (by omega : tree.nodes.data.size ≤ query.toNat)]
  have queryDifferent : query ≠ GeneralBorrowFreshMetadataChildDefaultSlot.index slot := by
    have firstNat : (GeneralBorrowFreshMetadataChildDefaultSlot.index slot).toNat = tree.tagMapping.mapping.size := by
      rw [indexEq]
      unfold GeneralBorrowFreshDefaultSequence.index
      cases slotShape : data.slot with
      | append oldEmpty oldAligned oldFits =>
        simp only [GeneralBorrowFreshDefaultStages.slot_index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 4294967296)]
      | reuse q available bounded vacant slack => rw [noFree] at available;cases available
    intro equal
    have eq := congrArg UniIndex.toNat equal
    omega
  have readClean := (GeneralBorrowFreshActiveOnRange.ranged tree protections data.parentTag parent data.root query
    (Size.ofBytes offset) (Size.ofBytes len) .Read .Write .VisitChildrenOfAccessed (fun _ => rfl)
    data.depth data.children data.parentNode data.parentPresent data.roots data.covered data.parentTagPresent
    vacant futureClean data.well offset (offset+len) owned bounds (Nat.le_refl _) (Nat.le_refl _)).2
  have afterClean : GeneralBorrowFreshFutureClean.Clean after query :=
    GeneralRootDefaultCleanSlot.mutable_slot accessed.tree depth children covered data.parentTag newTag parent data.parentNode
      tagPresent parentPresent fresh slot offset len nonzero good.2.2.1 bounded query queryDifferent readClean
  have cleanNext : GeneralBorrowFreshFutureClean.Clean after (GeneralBorrowFreshMutableStages.slot_index nextSlot) := by
    simpa only [nextSlot,GeneralBorrowFreshMutableStages.slot_index,mapSize,query] using afterClean
  let node := Classical.choose metadata.node
  have nodeFacts := Classical.choose_spec metadata.node
  have presentNode := nodeFacts.1
  change (GeneralBorrowFreshMetadataChildDefaultSlot.result accessed.tree data.parentTag newTag offset len).nodeAt (GeneralBorrowFreshMetadataChildDefaultSlot.index slot) = some node at presentNode
  rw [indexEq] at presentNode
  have childOwned := (GeneralBorrowFreshDefaultSequence.run tree newTag parent offset len data protections owned).2.2.1
  have targetActive := (GeneralBorrowFreshDefaultSequence.run_active tree newTag parent offset len data protections owned active).2.2.2.2
  let next : GenericAsMutPtrEntryValidity.Data after protections newTag nextTag offset len :=
    ⟨GeneralBorrowFreshDefaultSequence.index data,data.root,node,metadata.certificates.depth,
      metadata.certificates.children,presentNode,metadata.roots.trans (roots.trans data.roots),metadata.certificates.covered,
      (by simpa only [indexEq,sameTree] using metadata.lookup),freshNext,nodeFreshNext,metadata.nodeFits,nextSlot,metadata.well,childOwned⟩
  exact ⟨next,cleanNext,targetActive⟩
end DuplicatePrefix.GeneralRootDefaultNext
