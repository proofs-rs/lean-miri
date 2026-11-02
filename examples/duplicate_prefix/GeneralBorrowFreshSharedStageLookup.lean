import duplicate_prefix.GeneralBorrowFreshSharedStagePaths
namespace DuplicatePrefix.GeneralBorrowFreshSharedStageLookup
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshSharedSequence DuplicatePrefix.GeneralBorrowFreshReadFrame
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

/-- The actual parent Read leaves the tag map unchanged, and either real
shared allocator branch preserves every older tag lookup. -/
theorem old_lookup (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (query : BorTag) (different : newTag ≠ query) :
    (child data protections isProtected).tree.indexOfTag query = tree.indexOfTag query := by
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
  have metadata := GeneralBorrowFreshMetadataChildSlot.build accessed.tree depth children covered data.parentTag newTag parent data.parentNode
    tagPresent parentPresent fresh slot isProtected offset len data.nonzero good.2.2.1 bounds
  have same := metadata.oldLookup query different
  change (child data protections isProtected).tree.indexOfTag query = accessed.tree.indexOfTag query at same
  exact same.trans (congrArg (fun map => map.get query) mapping)

/-- Fresh initial tag-map data excludes equality with every present old tag. -/
theorem fresh_not_present (tree : BorrowTree) (tag old : BorTag) (index : UniIndex)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (present : tree.indexOfTag old = some index) : tag ≠ old := by
  have absent : tree.indexOfTag tag = none := by
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find tree.tagMapping tag fresh,Option.map_none]
  intro equal
  rw [equal,present] at absent
  cases absent
end DuplicatePrefix.GeneralBorrowFreshSharedStageLookup
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshSharedStageLookup." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved shared old tag lookup dependency {dependency}"
