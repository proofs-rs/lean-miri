import duplicate_prefix.GeneralBorrowForestForeignSharedResources
import duplicate_prefix.GeneralBorrowForestForeignSharedFresh

namespace DuplicatePrefix.GeneralBorrowForestForeignSharedHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestForeignAccess (LocationData)
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowForestForeignShared (read child)
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

abbrev Operation := BorTag × ChildrenVisitMode

def run (protections : ProtectedTags) (offset len : UInt64) :
    List Operation → BorrowTree → BorTag → BorrowTree × BorTag
  | [], tree, parentTag => (tree,parentTag)
  | operation::rest, tree, parentTag =>
      run protections offset len rest (child tree protections parentTag operation.1 false offset len operation.2).tree operation.1

def Completed (protections : ProtectedTags) (offset len : UInt64) :
    List Operation → BorrowTree → BorTag → Prop
  | [], _, _ => True
  | operation::rest, tree, parentTag =>
      (read tree protections parentTag offset len operation.2).status = .Completed ∧
      (child tree protections parentTag operation.1 false offset len operation.2).outcome = .ok () ∧
      Completed protections offset len rest (child tree protections parentTag operation.1 false offset len operation.2).tree operation.1

/-- Arbitrary finite REAL shared-child chains on a general multiple-root forest.
Every step performs its real bounded ranged Read then Frozen unprotected child
constructor, through the actual allocator's append/reuse choice. Modes may vary.
Only INITIAL graph, slice, allocator, distinct unused tags and finite node
headroom are premises. Every step's success, fresh-tag availability, full next
permission/cache/region records and allocator consistency are derived.
This does not yet permit choosing old bank handles or interleaving GC/exposure. -/
theorem complete (protections : ProtectedTags) (offset len : UInt64) (nonzero : len ≠ 0)
    (primary : UniIndex) (extras : List UniIndex) (operations : List Operation)
    (tree : BorrowTree) (parent : UniIndex) (parentTag : BorTag)
    (context : Context tree parent primary extras) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (allocator : GeneralBorrowGcAllocator.Invariant tree) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (before : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (LocationData tree location protections parent primary extras .Read))
      offset (offset+len) tree.locations)
    (unused : ∀ operation ∈ operations, GeneralBorrowTagMap.Fresh tree.tagMapping operation.1)
    (distinct : (operations.map Prod.fst).Nodup)
    (room : tree.nodes.size+operations.length+4 ≤ 4294967295) :
    Completed protections offset len operations tree parentTag ∧
    let final := run protections offset len operations tree parentTag
    ∃ anchor, Nonempty (Context final.1 anchor primary extras) ∧ final.1.indexOfTag final.2 = some anchor ∧
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (LocationData final.1 location protections anchor primary extras .Read))
        offset (offset+len) final.1.locations ∧
      GeneralBorrowGcAllocator.Invariant final.1 ∧ GeneralBorrowGraph.RootsCover final.1 ∧
      final.1.locations.WellFormed ∧ final.1.locations.size = tree.locations.size ∧
      final.1.nodes.size ≤ tree.nodes.size+operations.length := by
  induction operations generalizing tree parent parentTag with
  | nil =>
    exact ⟨True.intro,parent,⟨context⟩,parentTagPresent,before,allocator,covered,well,rfl,Nat.le_refl _⟩
  | cons operation rest ih =>
    have headFresh := unused operation (by simp)
    let depth := GeneralBorrowCanonicalParentDepth.normalize tree.nodes context.depth
    let normalized : Context tree parent primary extras := {context with depth := depth}
    have aligned := GeneralBorrowFreshStagePool.empty_aligned tree allocator.accounting
    have mappingFits : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295 := by
      intro empty
      rw [aligned empty]
      change tree.nodes.data.size + (operation::rest).length+4 ≤ _ at room
      omega
    let slot := GeneralBorrowCanonicalParentDepth.slot tree context.depth parent context.anchorNode context.anchorPresent
      allocator.pool aligned mappingFits
    have nodeFits : tree.nodes.data.size ≤ 4294967296 := by
      change tree.nodes.data.size + (operation::rest).length+4 ≤ _ at room
      omega
    have done := GeneralBorrowForestForeignShared.run tree protections parentTag operation.1 false parent primary extras offset len operation.2
      normalized covered parentTagPresent headFresh slot nodeFits nonzero well bounds before
    have resources := GeneralBorrowForestForeignSharedResources.preserves tree protections parentTag operation.1 false parent primary extras offset len operation.2
      normalized covered parentTagPresent headFresh slot nodeFits nonzero well bounds allocator before
    let nextTree := (child tree protections parentTag operation.1 false offset len operation.2).tree
    let nextParent := GeneralBorrowFreshMetadataChildSlot.index slot
    obtain ⟨nextContext⟩ := done.2.2.1
    have nextUnused : ∀ item ∈ rest, GeneralBorrowTagMap.Fresh nextTree.tagMapping item.1 := by
      intro item member
      have oldFresh := unused item (by simp [member])
      have different : operation.1 ≠ item.1 := by
        have unique := List.nodup_cons.mp (show (operation.1 :: rest.map Prod.fst).Nodup from distinct)
        intro equal
        exact unique.1 (equal ▸ List.mem_map.mpr ⟨item,member,rfl⟩)
      exact GeneralBorrowForestForeignSharedFresh.preserves tree protections parentTag operation.1 false parent primary extras offset len operation.2
        normalized covered parentTagPresent headFresh slot nodeFits nonzero well bounds before item.1 oldFresh different
    have nextDistinct : (rest.map Prod.fst).Nodup :=
      (List.nodup_cons.mp (show (operation.1 :: rest.map Prod.fst).Nodup from distinct)).2
    have nextRoom : nextTree.nodes.size+rest.length+4 ≤ 4294967295 := by
      have growth := resources.2.2.2.1
      change nextTree.nodes.size ≤ tree.nodes.size+1 at growth
      simp only [List.length_cons] at room
      omega
    have nextBounds : offset.toNat+len.toNat ≤ nextTree.locations.size.bytes.toNat := by
      rw [show nextTree.locations.size = tree.locations.size from resources.2.2.1]
      exact bounds
    obtain ⟨tail,anchor,finalContext,finalTag,finalOwners,finalAllocator,finalCovered,finalWell,capacity,growth⟩ :=
      ih nextTree nextParent operation.1 nextContext resources.2.2.2.2.1 resources.2.2.2.2.2
        resources.1 resources.2.1 nextBounds done.2.2.2 nextUnused nextDistinct nextRoom
    refine ⟨⟨done.1,done.2.1,tail⟩,anchor,finalContext,finalTag,finalOwners,finalAllocator,finalCovered,finalWell,
      capacity.trans resources.2.2.1,?_⟩
    have count := resources.2.2.2.1
    change nextTree.nodes.size ≤ tree.nodes.size+1 at count
    change (run protections offset len rest nextTree operation.1).1.nodes.size ≤ tree.nodes.size+(operation::rest).length
    simp only [List.length_cons]
    omega

end DuplicatePrefix.GeneralBorrowForestForeignSharedHistory
