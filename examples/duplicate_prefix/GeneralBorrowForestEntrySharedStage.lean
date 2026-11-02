import duplicate_prefix.GeneralBorrowForestEntryMixed
import duplicate_prefix.GeneralBorrowForestMixedShared

namespace DuplicatePrefix.GeneralBorrowForestEntrySharedStage
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The mutable FnEntry child's ownership derives the real unprotected shared
expression Read/Frozen construction and its exact child-relative mixed labels. -/
theorem run (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64)
    (context : GeneralBorrowForestAccessData.Context tree parent primary extras)
    (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag parentTag = some parent)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (slot : GeneralBorrowFreshReborrowStages.Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (nonzero : len ≠ 0)
    (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (before : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data tree location protections parent primary extras))
      offset (offset+len) tree.locations) :
    let accessed := GeneralBorrowForestMixedShared.read tree protections parentTag offset len .VisitChildrenOfAccessed
    let child := GeneralBorrowForestMixedShared.child tree protections parentTag newTag false offset len .VisitChildrenOfAccessed
    accessed.status = .Completed ∧ child.outcome = .ok () ∧
      Nonempty (GeneralBorrowForestAccessData.Context child.tree (GeneralBorrowFreshMetadataChildSlot.index slot) primary extras) ∧
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data child.tree location protections
          (GeneralBorrowFreshMetadataChildSlot.index slot) primary extras
          (GeneralBorrowFreshMixedChild.extend (fun _ => true) (GeneralBorrowFreshMetadataChildSlot.index slot).toNat)))
        offset (offset+len) child.tree.locations := by
  exact GeneralBorrowForestMixedShared.run tree protections parentTag newTag false parent primary extras offset len
    .VisitChildrenOfAccessed context covered tagPresent fresh slot fits (fun _ => true) nonzero well bounds
    (GeneralBorrowForestEntryMixed.owned tree protections parent primary extras offset (offset+len) before)

end DuplicatePrefix.GeneralBorrowForestEntrySharedStage
