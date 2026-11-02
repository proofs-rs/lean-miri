import duplicate_prefix.GeneralBorrowForestDefaultConstructorNext
import duplicate_prefix.GeneralBorrowFreshDefaultSlotCacheWitness
import duplicate_prefix.GeneralBorrowFreshDefaultSlotOwned
import duplicate_prefix.GeneralBorrowForestMutableAccess
import duplicate_prefix.GeneralBorrowFreshMetadataChildDefaultOld

namespace DuplicatePrefix.GeneralBorrowForestDefaultConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestMutableAccess (Data)
open GeneralBorrowForestAccessData (Context)
open GeneralBorrowFreshReborrowStages (Slot)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The REAL Default mutable reservation forms ALL of its new child's next slice-local
input records, including foreign-region support, exact BOTH-kind zero-cache facts and
graph-only ancestor exclusion. Its actual graph context is formed as well.
Every permission/cache/graph postcondition and constructor completion is derived
from initial records. No result-ownership/cache/success premise is supplied.
This is the constructor stage; its leading ranged Read is joined separately. -/
theorem construct (tree : BorrowTree) (protections : ProtectedTags) (newTag : BorTag)
    (parentTag : BorTag) (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64)
    (context : Context tree parent primary extras) (covered : GeneralBorrowGraph.RootsCover tree)
    (parentTagPresent : tree.indexOfTag parentTag = some parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (slot : Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (before : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (Data tree location protections parent primary extras))
      offset (offset+len) tree.locations) :
    let result := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    result.outcome = .ok () ∧
      Nonempty (Context result.tree (GeneralBorrowFreshMetadataChildDefaultSlot.index slot) primary extras) ∧
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (Data result.tree location protections
          (GeneralBorrowFreshMetadataChildDefaultSlot.index slot) primary extras))
        offset (offset+len) result.tree.locations := by
  let predicate := fun location => Nonempty (Data tree location protections parent primary extras)
  have parentOwners : GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write)
      offset (offset+len) tree.locations := by
    intro position valid positive lower upper
    obtain ⟨data⟩ := before position valid positive lower upper
    exact ⟨⟨data.base.forest⟩,data.base.owned⟩
  have childOwners := GeneralBorrowFreshDefaultSlotOwned.owned tree context.depth parentTag newTag parent context.anchorNode
    parentTagPresent context.anchorPresent fresh slot fits offset len nonzero well bounds protections parentOwners
  have cacheOrigins := GeneralBorrowFreshDefaultSlotCacheWitness.owned tree context.depth context.children covered parentTag newTag parent context.anchorNode
    parentTagPresent context.anchorPresent fresh slot offset len nonzero well bounds predicate before
  let metadata := GeneralBorrowFreshMetadataChildDefaultSlot.build tree context.depth context.children covered parentTag newTag parent context.anchorNode
    parentTagPresent context.anchorPresent fresh slot offset len nonzero well fits bounds
  obtain ⟨newNode,newPresent,newTagEq,newFlag⟩ := metadata.node
  obtain ⟨nextPrimary,primaryPresent,primaryTag,primaryFlag⟩ := GeneralBorrowFreshMetadataChildDefaultOld.of_slot
    tree context.depth context.children covered parentTag newTag parent context.anchorNode parentTagPresent context.anchorPresent fresh slot
    offset len nonzero well bounds primary context.primaryNode context.primaryPresent
  have flags := GeneralBorrowFreshDefaultSlotFlags.of_slot tree context.depth context.children covered parentTag newTag parent context.anchorNode
    parentTagPresent context.anchorPresent fresh slot offset len nonzero well bounds context.unexposed
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
    obtain ⟨base,supportEq⟩ := GeneralBorrowForestDefaultConstructorNext.next tree context.depth context.children covered parentTag newTag parent primary
      context.anchorNode extras parentTagPresent context.anchorPresent fresh slot offset len nonzero well bounds
      original _ protections data.base context.unexposed (childOwners.2 position valid positive lower upper) cache
    refine ⟨{
      base := base
      readZero := ?_ }⟩
    intro index member
    rw [supportEq] at member
    have equalCache : (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree.locations.entries[position].data.exposedCache = original.exposedCache := cache
    rw [equalCache]
    exact data.readZero index member

end DuplicatePrefix.GeneralBorrowForestDefaultConstructor
