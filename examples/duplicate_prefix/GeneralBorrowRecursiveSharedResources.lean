import duplicate_prefix.GeneralBorrowCanonicalParentDepth
import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant
import duplicate_prefix.GeneralBorrowFreshSharedVacantClean

namespace DuplicatePrefix.GeneralBorrowRecursiveSharedResources
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowFreshSharedSequence
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

set_option autoImplicit false in
/-- Metadata/resources for arbitrary-depth recurring shared generation. No star,
fixed parent depth, successful operation or permission ownership is a field. -/
structure Resources (tree : BorrowTree) (root : UniIndex) where
  depth : ParentDepth tree.nodes
  children : GeneralBorrowGraph.ChildNodes tree
  covered : GeneralBorrowGraph.RootsCover tree
  roots : tree.roots = #[root]
  allocator : GeneralBorrowGcAllocator.Invariant tree
  clean : GeneralBorrowGcVacantClean.VacantClean tree
  well : tree.locations.WellFormed
  room : tree.nodes.size+4 ≤ 4294967295

/-- Form a real append/reuse Data record at any present parent. Canonical rank
compression internally supplies strict reuse slack at arbitrary graph depth. -/
def data (tree : BorrowTree) (root : UniIndex) (resources : Resources tree root)
    (parent : UniIndex) (node : TreeNode) (present : tree.nodeAt parent = some node)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    Data tree tag parent offset len := by
  let depth := GeneralBorrowCanonicalParentDepth.normalize tree.nodes resources.depth
  have aligned := GeneralBorrowFreshStagePool.empty_aligned tree resources.allocator.accounting
  have fits : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295 := by
    intro empty
    rw [aligned empty]
    have room := resources.room
    change tree.nodes.data.size+4 ≤ _ at room
    omega
  let slot := GeneralBorrowCanonicalParentDepth.slot tree resources.depth parent node present resources.allocator.pool aligned fits
  exact {
    parentTag := node.tag,root := root,parentNode := node,depth := depth
    children := resources.children,parentPresent := present,roots := resources.roots,covered := resources.covered
    parentTagPresent := resources.allocator.nodeTags parent node present,tagFresh := fresh
    protectorFresh := by
      intro row member same
      have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
      have lookup := resources.allocator.nodeTags row.1 row.2 present
      have absent : tree.tagMapping.get tag = none := by
        unfold UniKeyMap.get
        rw [GeneralBorrowTagMap.fresh_find tree.tagMapping tag fresh]
        rfl
      rw [same,absent] at lookup
      cases lookup
    nodeFits := by have room := resources.room;change tree.nodes.data.size+4 ≤ _ at room;omega
    slot := slot,nonzero := nonzero,well := resources.well,bounds := bounds
    clean := resources.clean _ (GeneralBorrowFreshSharedWithinStages.slot_vacant tree depth parent slot) }

/-- One actual shared stage retains structural resources for ANY later present
parent, including its new child at a greater depth. Success, metadata, allocator
and vacant Clean are derived from the initial resources and local ownership.
Only next-allocation headroom is an extra numeric resource. -/
theorem advance (tree : BorrowTree) (root : UniIndex) (resources : Resources tree root)
    (parent : UniIndex) (node : TreeNode) (present : tree.nodeAt parent = some node)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (room : tree.nodes.size+5 ≤ 4294967295) :
    let supplied := data tree root resources parent node present tag fresh offset len nonzero bounds
    (read supplied protections isProtected).status = .Completed ∧
    (child supplied protections isProtected).outcome = .ok () ∧
    Nonempty (Resources (child supplied protections isProtected).tree root) ∧
    OwnedOn (Combined (child supplied protections isProtected).tree (registered protections tag isProtected)
      (index supplied) (GeneralBorrowFreshMixedChild.extend writable (index supplied).toNat))
      offset (offset+len) (child supplied protections isProtected).tree.locations ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin (child supplied protections isProtected).tree (index supplied) .Read offset (offset+len) := by
  dsimp only
  let supplied := data tree root resources parent node present tag fresh offset len nonzero bounds
  have completed := GeneralBorrowFreshSharedSequence.run tree tag parent offset len supplied protections isProtected writable owned
  let metadata := GeneralBorrowFreshStageMetadata.build tree tag parent offset len supplied protections isProtected writable owned
  have allocator := (GeneralBorrowSharedAllocatorInvariant.shared_stage tree tag parent offset len supplied protections isProtected writable owned resources.allocator).2.2
  have clean := (GeneralBorrowFreshSharedVacantClean.stage tree tag parent offset len supplied protections isProtected writable owned resources.clean).2.2
  have capacity : (child supplied protections isProtected).tree.nodes.size ≤ tree.nodes.size+1 := by
    let location : LocationTree := ⟨⟨#[]⟩,{}⟩
    have extension := metadata.extension location location protections
    have beforeSize : (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map,UniValMap.size]
    have afterSize : (source_normal_projection (child supplied protections isProtected).tree location protections).topology.nodes.size =
        (child supplied protections isProtected).tree.nodes.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map,UniValMap.size]
    rcases extension with appended | reused
    · have count := appended.length
      rw [beforeSize,afterSize] at count
      omega
    · have count := reused.length
      rw [beforeSize,afterSize] at count
      omega
  have nextRoom : (child supplied protections isProtected).tree.nodes.size+4 ≤ 4294967295 := by omega
  exact ⟨completed.1,completed.2.1,
    ⟨⟨metadata.certificates.depth,metadata.certificates.children,metadata.certificates.covered,
      metadata.roots.trans resources.roots,allocator,clean,metadata.well,by simpa only [supplied] using nextRoom⟩⟩,
    completed.2.2.1,completed.2.2.2⟩

/-- Internally form the next real constructor Data at the newly generated
child, at ANY input graph depth. All poststate graph/allocator/Clean/rank facts
come from the actual first stage; the next parent tag is proved to be its tag. -/
noncomputable def childData (tree : BorrowTree) (root : UniIndex) (resources : Resources tree root)
    (parent : UniIndex) (node : TreeNode) (present : tree.nodeAt parent = some node)
    (tag nextTag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (nextFresh : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag) (different : tag ≠ nextTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (isProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (room : tree.nodes.size+5 ≤ 4294967295) :
    let supplied := data tree root resources parent node present tag fresh offset len nonzero bounds
    {next : Data (child supplied protections isProtected).tree nextTag (index supplied) offset len // next.parentTag = tag} := by
  dsimp only
  let supplied := data tree root resources parent node present tag fresh offset len nonzero bounds
  have facts := advance tree root resources parent node present tag fresh offset len nonzero bounds protections isProtected writable owned room
  let metadata := GeneralBorrowFreshStageMetadata.build tree tag parent offset len supplied protections isProtected writable owned
  let post := Classical.choice facts.2.2.1
  let childNode := Classical.choose metadata.node
  have childPresent := (Classical.choose_spec metadata.node).1
  have childTag := (Classical.choose_spec metadata.node).2.1
  have available := metadata.freshTag nextTag nextFresh different
  have request : offset.toNat+len.toNat ≤ (child supplied protections isProtected).tree.locations.size.bytes.toNat := by
    rw [metadata.capacity];exact bounds
  exact ⟨data _ root post (index supplied) childNode childPresent nextTag available offset len nonzero request,childTag⟩

/-- A real second shared stage can use the internally formed child Data at any
initial depth; no next Data, next ownership or successful operation is assumed. -/
theorem descend (tree : BorrowTree) (root : UniIndex) (resources : Resources tree root)
    (parent : UniIndex) (node : TreeNode) (present : tree.nodeAt parent = some node)
    (tag nextTag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (nextFresh : GeneralBorrowTagMap.Fresh tree.tagMapping nextTag) (different : tag ≠ nextTag)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (isProtected nextProtected : Bool) (writable : Nat → Bool)
    (owned : OwnedOn (Combined tree protections parent writable) offset (offset+len) tree.locations)
    (room : tree.nodes.size+5 ≤ 4294967295) :
    let supplied := data tree root resources parent node present tag fresh offset len nonzero bounds
    let next := childData tree root resources parent node present tag nextTag fresh nextFresh different offset len nonzero bounds protections isProtected writable owned room
    (read supplied protections isProtected).status = .Completed ∧
    (child supplied protections isProtected).outcome = .ok () ∧
    next.val.parentTag = tag ∧
    (read next.val (registered protections tag isProtected) nextProtected).status = .Completed ∧
    (child next.val (registered protections tag isProtected) nextProtected).outcome = .ok () := by
  dsimp only
  let supplied := data tree root resources parent node present tag fresh offset len nonzero bounds
  let next := childData tree root resources parent node present tag nextTag fresh nextFresh different offset len nonzero bounds protections isProtected writable owned room
  have first := advance tree root resources parent node present tag fresh offset len nonzero bounds protections isProtected writable owned room
  have second := GeneralBorrowFreshSharedSequence.run (child supplied protections isProtected).tree nextTag (index supplied) offset len
    next.val (registered protections tag isProtected) nextProtected (GeneralBorrowFreshMixedChild.extend writable (index supplied).toNat) first.2.2.2.1
  exact ⟨first.1,first.2.1,next.property,second.1,second.2.1⟩

end DuplicatePrefix.GeneralBorrowRecursiveSharedResources
