import duplicate_prefix.GeneralBorrowFreshStageMetadata
import duplicate_prefix.GeneralBorrowFreshMetadataChildOld
import duplicate_prefix.GeneralBorrowFreshSharedPaths
namespace DuplicatePrefix.GeneralBorrowFreshSharedStagePaths
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseMixed
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshReadFrame
open DuplicatePrefix.GeneralBorrowFreshReborrowStages DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

theorem old_node (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (query : UniIndex) (oldNode : TreeNode) (present : tree.nodeAt query = some oldNode) :
    ∃ next, (child data protections isProtected).tree.nodeAt query = some next ∧
      next.tag = oldNode.tag ∧ next.isExposed = oldNode.isExposed := by
  let accessed := read data protections isProtected
  have owners := GeneralBorrowFreshStageMetadata.registered_owned tree newTag parent offset len data protections isProtected writable owned
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
  have oldPresent : accessed.tree.nodeAt query = some oldNode := by
    change accessed.tree.nodes.get query = some oldNode
    rw [nodes]
    exact present
  exact GeneralBorrowFreshMetadataChildOld.of_slot accessed.tree depth children covered data.parentTag newTag parent data.parentNode
    tagPresent parentPresent fresh slot isProtected offset len data.nonzero good.2.2.1 bounds query oldNode oldPresent

theorem topology_any (tree : BorrowTree) (first second : LocationTree) (firstTags secondTags : ProtectedTags) :
    (source_normal_projection tree first firstTags).topology = (source_normal_projection tree second secondTags).topology := by
  unfold_general_projection
  rfl

noncomputable def forest (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (location : LocationTree) (tags : ProtectedTags) :
    GeneralBorrowForest.Forest (source_normal_projection tree location tags).topology := by
  apply Classical.choice
  have lenNonzero : len.toNat ≠ 0 := fun zero => data.nonzero (UInt64.toNat_inj.mp (by simpa using zero))
  have lenPositive : 0 < len.toNat := by omega
  have sizeBound : tree.locations.size.bytes.toNat < 2^64 := UInt64.toNat_lt_size tree.locations.size.bytes
  have addition : (offset+len).toNat = offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by have bounds := data.bounds;omega)]
  have inside : offset.toNat < tree.locations.size.bytes.toNat := by have bounds := data.bounds;omega
  obtain ⟨position,valid,lower,upper⟩ := GeneralRangeMapGeometry.covered tree.locations data.well offset inside
  have contract := owned position valid (by omega) (by omega) upper
  obtain ⟨available⟩ := contract.1.1
  rw [←topology_any tree tree.locations.entries[position].data location protections tags]
  exact ⟨available⟩

theorem index_at_end (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (noFree : tree.tagMapping.deassigned.back? = none) :
    (index data).toNat = tree.nodes.data.size := by
  cases slotEq : data.slot with
  | append empty aligned fits =>
    simp only [index,GeneralBorrowFreshSharedWithinStages.slot_index,slotEq,UniIndex.toNat,UInt32.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
    exact aligned
  | reuse candidate available bounded vacant slack => rw [noFree] at available;cases available

/-- The actual stage has a complete ancestor-path attachment, derived from the
initial positive owned slice and append allocator data. -/
theorem attach (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (noFree : tree.tagMapping.deassigned.back? = none)
    (oldLocation newLocation : LocationTree) (tags : ProtectedTags) :
    GeneralBorrowFreshSharedPaths.Attach (source_normal_projection tree oldLocation tags).topology
      (source_normal_projection (child data protections isProtected).tree newLocation tags).topology
      parent.toNat (index data).toNat := by
  have atEnd := index_at_end tree newTag parent offset len data noFree
  have projectedSize : (source_normal_projection tree oldLocation tags).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection
    unfold_general_topology
    simp only [Array.size_map]
  have extension := (GeneralBorrowFreshStageMetadata.build tree newTag parent offset len data protections isProtected writable owned).extension oldLocation newLocation tags
  rcases extension with appended | reused
  · rw [atEnd,←projectedSize]
    exact GeneralBorrowFreshSharedPaths.of_append _ _ _ appended (forest tree newTag parent offset len data protections writable owned oldLocation tags)
  · have impossible := reused.valid
    rw [atEnd,projectedSize] at impossible
    omega
end DuplicatePrefix.GeneralBorrowFreshSharedStagePaths
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshSharedStagePaths." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual stage path dependency {dependency}"
