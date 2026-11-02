import duplicate_prefix.GeneralBorrowForestForeignConstructorNext
import duplicate_prefix.GeneralBorrowFreshSharedSlotCacheWitness
import duplicate_prefix.GeneralBorrowFreshSharedSlotOwned

namespace DuplicatePrefix.GeneralBorrowForestForeignSharedConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestForeignAccess (LocationData)
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The REAL Frozen constructor forms ALL of its new child's next slice-local
input records, including foreign-region support, exact zero-cache facts and
graph-only ancestor exclusion. Its actual graph context is formed as well.
Every permission/cache/graph postcondition and constructor completion is derived
from initial records. No result-ownership/cache/success premise is supplied.
This is the constructor stage; its leading ranged Read is joined separately. -/
theorem construct (tree : BorrowTree) (protections : ProtectedTags) (newTag : BorTag) (isProtected : Bool)
    (parentTag : BorTag) (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64)
    (context : Context tree parent primary extras) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (before : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (LocationData tree location protections parent primary extras .Read))
      offset (offset+len) tree.locations) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen isProtected
    result.outcome = .ok () ∧
      Nonempty (Context result.tree (GeneralBorrowFreshMetadataChildSlot.index slot) primary extras) ∧
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (LocationData result.tree location protections
          (GeneralBorrowFreshMetadataChildSlot.index slot) primary extras .Read))
        offset (offset+len) result.tree.locations := by
  let predicate := fun location => Nonempty (LocationData tree location protections parent primary extras .Read)
  have parentOwners : GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Read)
      offset (offset+len) tree.locations := by
    intro position valid positive lower upper
    obtain ⟨data⟩ := before position valid positive lower upper
    exact ⟨⟨data.forest⟩,data.owned⟩
  have childOwners := GeneralBorrowFreshSharedSlotOwned.owned tree context.depth parentTag newTag parent context.anchorNode
    parentTagPresent context.anchorPresent fresh slot fits isProtected offset len nonzero well bounds protections parentOwners
  have cacheOrigins := GeneralBorrowFreshSharedSlotCacheWitness.owned tree context.depth context.children covered parentTag newTag parent context.anchorNode
    parentTagPresent context.anchorPresent fresh slot isProtected offset len nonzero well bounds predicate before
  let metadata := GeneralBorrowFreshMetadataChildSlot.build tree context.depth context.children covered parentTag newTag parent context.anchorNode
    parentTagPresent context.anchorPresent fresh slot isProtected offset len nonzero well bounds
  obtain ⟨newNode,newPresent,newTagEq,newFlag⟩ := metadata.node
  obtain ⟨nextPrimary,primaryPresent,primaryTag,primaryFlag⟩ := GeneralBorrowFreshMetadataChildOld.of_slot
    tree context.depth context.children covered parentTag newTag parent context.anchorNode parentTagPresent context.anchorPresent fresh slot
    isProtected offset len nonzero well bounds primary context.primaryNode context.primaryPresent
  have flags := GeneralBorrowFreshSharedSlotFlags.of_slot tree context.depth context.children covered parentTag newTag parent context.anchorNode
    parentTagPresent context.anchorPresent fresh slot isProtected offset len nonzero well bounds context.unexposed
  refine ⟨childOwners.1,?_,?_⟩
  · exact ⟨{
      anchorNode := newNode
      primaryNode := nextPrimary
      depth := metadata.certificates.depth
      children := metadata.certificates.children
      anchorPresent := newPresent
      primaryPresent := primaryPresent
      roots := metadata.roots.trans context.roots
      different := context.different
      unexposed := flags }⟩
  · intro position valid positive lower upper
    obtain ⟨original,⟨data⟩,cache⟩ := cacheOrigins position valid positive lower upper
    exact GeneralBorrowForestForeignConstructorNext.next tree context.depth context.children covered parentTag newTag parent primary
      context.anchorNode extras parentTagPresent context.anchorPresent fresh slot isProtected offset len nonzero well bounds
      original _ protections data context.unexposed (childOwners.2 position valid positive lower upper) cache

end DuplicatePrefix.GeneralBorrowForestForeignSharedConstructor
