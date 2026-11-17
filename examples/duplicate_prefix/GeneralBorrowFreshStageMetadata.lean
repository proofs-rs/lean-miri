import duplicate_prefix.GeneralBorrowFreshSharedSequence
import duplicate_prefix.GeneralBorrowFreshSharedGeometry
import duplicate_prefix.GeneralBorrowFreshMetadataChildProtector
import duplicate_prefix.GeneralBorrowFreshSharedFutureClean
namespace DuplicatePrefix.GeneralBorrowFreshStageMetadata
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshReadFrame
open DuplicatePrefix.GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 800000

theorem registered_owned (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations) :
    OwnedOn (Combined tree (registered protections newTag isProtected) parent writable) offset (offset+len) tree.locations := by
  cases isProtected with
  | false => exact owned
  | true =>
    intro position valid positive lower upper
    have previous := owned position valid positive lower upper
    simp only [registered,↓reduceIte]
    unfold Combined GeneralBorrowRange.LocationOwned Mixed at previous ⊢
    rw [GeneralBorrowProtector.normal_projection tree _ protections newTag .StrongProtector data.protectorFresh]
    exact previous

structure Output (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) where
  certificates : GeneralBorrowFreshMetadataChildAttach.Certificates (child data protections isProtected).tree
  roots : (child data protections isProtected).tree.roots = tree.roots
  lookup : (child data protections isProtected).tree.indexOfTag newTag = some (index data)
  node : ∃ node, (child data protections isProtected).tree.nodeAt (index data) = some node ∧ node.tag = newTag ∧ node.isExposed = false
  well : (child data protections isProtected).tree.locations.WellFormed
  capacity : (child data protections isProtected).tree.locations.size = tree.locations.size
  allocator : tree.tagMapping.deassigned.back? = none →
    (child data protections isProtected).tree.tagMapping.deassigned.back? = none ∧
    (child data protections isProtected).tree.tagMapping.mapping.size = (child data protections isProtected).tree.nodes.data.size ∧
    (child data protections isProtected).tree.tagMapping.mapping.size = tree.tagMapping.mapping.size+1
  freshTag : ∀ next, GeneralBorrowTagMap.Fresh tree.tagMapping next → newTag ≠ next →
    GeneralBorrowTagMap.Fresh (child data protections isProtected).tree.tagMapping next
  freshProtector : ∀ next, GeneralBorrowProtector.Fresh tree next → newTag ≠ next →
    GeneralBorrowProtector.Fresh (child data protections isProtected).tree next
  futureClean : ∀ query, tree.nodes.get query = none → query ≠ index data →
    GeneralBorrowFreshFutureClean.Clean tree query →
    GeneralBorrowFreshFutureClean.Clean (child data protections isProtected).tree query
  extension : ∀ oldLocation newLocation tags,
    GeneralBorrowFreshTopology.Extension (source_normal_projection tree oldLocation tags).topology
      (source_normal_projection (child data protections isProtected).tree newLocation tags).topology parent.toNat ∨
    GeneralBorrowFreshReuseTopology.Extension (source_normal_projection tree oldLocation tags).topology
      (source_normal_projection (child data protections isProtected).tree newLocation tags).topology (index data).toNat parent.toNat

def build (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations) :
    Output tree newTag parent offset len data protections isProtected := by
  let accessed := read data protections isProtected
  have owners := registered_owned tree newTag parent offset len data protections isProtected writable owned
  have good := GeneralBorrowFreshMixedRead.access tree (registered protections newTag isProtected) data.parentTag parent data.root
    (Size.ofBytes offset) (Size.ofBytes len) writable .VisitChildrenOfAccessed data.nodeFits data.depth data.children data.parentNode
    data.parentPresent data.roots data.covered data.parentTagPresent data.well offset (offset+len) owners data.bounds
    (Nat.le_refl _) (Nat.le_refl _)
  change accessed.status = .Completed ∧ OwnedOn (Combined accessed.tree (registered protections newTag isProtected) parent writable)
    offset (offset+len) accessed.tree.locations ∧ accessed.tree.locations.WellFormed ∧ accessed.tree.locations.size = tree.locations.size at good
  have framed := GeneralBorrowFreshReadFrame.frame tree (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (registered protections newTag isProtected) .VisitChildrenOfAccessed
  change accessed.tree = {tree with locations := accessed.tree.locations} at framed
  have nodeEq := congrArg BorrowTree.nodes framed
  have nodes : accessed.tree.nodes = tree.nodes := nodeEq
  have mappingEq := congrArg BorrowTree.tagMapping framed
  have mapping : accessed.tree.tagMapping = tree.tagMapping := mappingEq
  have rootsEq := congrArg BorrowTree.roots framed
  have roots : accessed.tree.roots = tree.roots := rootsEq
  let depth := depth_on tree accessed.tree nodes data.depth
  have children : GeneralBorrowGraph.ChildNodes accessed.tree := by rw [framed];exact data.children
  have covered : GeneralBorrowGraph.RootsCover accessed.tree := by rw [framed];exact data.covered
  have parentPresent : accessed.tree.nodeAt parent = some data.parentNode := by change accessed.tree.nodes.get parent = _;rw [nodes];exact data.parentPresent
  have tagPresent : accessed.tree.tagMapping.get data.parentTag = some parent := by rw [mapping];exact data.parentTagPresent
  have fresh : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping newTag := by rw [mapping];exact data.tagFresh
  have bounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by rw [good.2.2.2];exact data.bounds
  let slot := GeneralBorrowFreshMetadataChildSlot.transport tree accessed.tree data.depth depth nodes mapping rfl parent data.slot
  have indexEq : GeneralBorrowFreshMetadataChildSlot.index slot = index data :=
    GeneralBorrowFreshMetadataChildSlot.transport_index tree accessed.tree data.depth depth nodes mapping rfl parent data.slot
  have metadata :=  GeneralBorrowFreshMetadataChildSlot.build accessed.tree depth children covered data.parentTag newTag parent data.parentNode
    tagPresent parentPresent fresh slot isProtected offset len data.nonzero good.2.2.1 bounds
  have locationFrame : (child data protections isProtected).tree.locations.WellFormed ∧
      (child data protections isProtected).tree.locations.size = accessed.tree.locations.size ∧
      (tree.tagMapping.deassigned.back? = none →
        (child data protections isProtected).tree.tagMapping.deassigned.back? = none ∧
        (child data protections isProtected).tree.tagMapping.mapping.size = (child data protections isProtected).tree.nodes.data.size ∧
        (child data protections isProtected).tree.tagMapping.mapping.size = tree.tagMapping.mapping.size+1) ∧
      (∀ next, GeneralBorrowTagMap.Fresh tree.tagMapping next → newTag ≠ next →
        GeneralBorrowTagMap.Fresh (child data protections isProtected).tree.tagMapping next) := by
    cases data.slot with
    | append noFree aligned fits =>
      let input : GeneralBorrowFreshMetadataChildShared.Input :=
        ⟨accessed.tree,depth,children,covered,data.parentTag,newTag,parent,data.parentNode,tagPresent,parentPresent,fresh,
          by rw [mapping];exact noFree,by rw [mapping,nodes];exact aligned,by rw [mapping];exact fits,
          isProtected,offset,len,data.nonzero,good.2.2.1,bounds⟩
      have geometry := GeneralBorrowFreshSharedGeometry.append_frame input
      have added := GeneralBorrowFreshMetadataChildShared.append input
      refine ⟨geometry.1,geometry.2,?_,?_⟩
      · intro empty
        refine ⟨added.noFree,added.aligned,?_⟩
        change (GeneralBorrowFreshMetadataChildShared.result input).tagMapping.mapping.size = tree.tagMapping.mapping.size+1
        rw [added.mapping]
        simp only [GeneralBorrowFreshMetadataChildShared.mapping,Array.size_push,input,mapping]
      · intro next oldFresh different
        exact GeneralBorrowFreshMetadataChildAllocator.append_fresh input next (by rw [mapping];exact oldFresh) different
    | reuse query available bounded vacant slack =>
      let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
        ⟨accessed.tree,depth,children,covered,data.parentTag,newTag,parent,data.parentNode,tagPresent,parentPresent,fresh,
          query,by rw [mapping];exact available,by rw [nodes];exact bounded,by rw [nodes];exact vacant,
          by change data.depth.depth parent < accessed.tree.nodes.size;rw [nodes];exact slack,
          isProtected,offset,len,data.nonzero,good.2.2.1,bounds⟩
      have geometry := GeneralBorrowFreshSharedGeometry.reuse_frame input
      refine ⟨geometry.1,geometry.2,?_,?_⟩
      · intro empty
        rw [empty] at available
        cases available
      · intro next oldFresh different
        exact GeneralBorrowFreshMetadataChildAllocator.reuse_fresh input next (by rw [mapping];exact oldFresh) different
  refine ⟨metadata.certificates,metadata.roots.trans roots,?_,?_,locationFrame.1,locationFrame.2.1.trans good.2.2.2,
    locationFrame.2.2.1,locationFrame.2.2.2,?_,?_,?_⟩
  · rw [←indexEq];exact metadata.lookup
  · rw [←indexEq];exact metadata.node
  · intro next oldFresh different
    have readFresh : GeneralBorrowProtector.Fresh accessed.tree next := by
      unfold GeneralBorrowProtector.Fresh
      rw [nodes]
      exact oldFresh
    exact GeneralBorrowFreshMetadataChildProtector.of_slot accessed.tree depth children covered data.parentTag newTag parent
      data.parentNode tagPresent parentPresent fresh slot isProtected offset len data.nonzero good.2.2.1 bounds next readFresh different
  · intro query vacant different clean
    have readOwners : OwnedOn (GeneralBorrowRange.LocationOwned tree (registered protections newTag isProtected) parent .Read)
        offset (offset+len) tree.locations := by
      intro position valid positive lower upper
      exact (owners position valid positive lower upper).1
    have cleanResult := GeneralBorrowFreshActiveOnRange.ranged tree (registered protections newTag isProtected) data.parentTag
      parent data.root query (Size.ofBytes offset) (Size.ofBytes len) .Read .Read .VisitChildrenOfAccessed (fun _ => rfl)
      data.depth data.children data.parentNode data.parentPresent data.roots data.covered data.parentTagPresent
      vacant clean data.well offset (offset+len) readOwners data.bounds (Nat.le_refl _) (Nat.le_refl _)
    have cleanAfter : GeneralBorrowFreshFutureClean.Clean accessed.tree query := cleanResult.2
    cases slotEq : data.slot with
    | append noFree aligned fits =>
      let input : GeneralBorrowFreshMetadataChildShared.Input :=
        ⟨accessed.tree,depth,children,covered,data.parentTag,newTag,parent,data.parentNode,tagPresent,parentPresent,fresh,
          by rw [mapping];exact noFree,by rw [mapping,nodes];exact aligned,by rw [mapping];exact fits,
          isProtected,offset,len,data.nonzero,good.2.2.1,bounds⟩
      have distinct : query ≠ GeneralBorrowFreshMetadataChildShared.index input := by
        simpa only [index,GeneralBorrowFreshSharedWithinStages.slot_index,slotEq,
          GeneralBorrowFreshMetadataChildShared.index,input,mapping] using different
      exact GeneralBorrowFreshSharedFutureClean.append input query distinct cleanAfter
    | reuse candidate available bounded vacantIndex slack =>
      let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
        ⟨accessed.tree,depth,children,covered,data.parentTag,newTag,parent,data.parentNode,tagPresent,parentPresent,fresh,
          candidate,by rw [mapping];exact available,by rw [nodes];exact bounded,by rw [nodes];exact vacantIndex,
          by change data.depth.depth parent < accessed.tree.nodes.size;rw [nodes];exact slack,
          isProtected,offset,len,data.nonzero,good.2.2.1,bounds⟩
      have distinct : query ≠ input.index := by
        simpa only [index,GeneralBorrowFreshSharedWithinStages.slot_index,slotEq,input] using different
      exact GeneralBorrowFreshSharedFutureClean.reuse input query distinct cleanAfter
  · intro oldLocation newLocation tags
    have topology := GeneralBorrowFreshMetadataChildAllocator.topology_frame tree accessed.tree nodes oldLocation oldLocation tags
    have extension := metadata.extension oldLocation newLocation tags
    rw [topology,indexEq] at extension
    exact extension
end DuplicatePrefix.GeneralBorrowFreshStageMetadata
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshStageMetadata." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved stage metadata dependency {dependency}"
