import duplicate_prefix.GeneralBorrowFreshRegistration
import duplicate_prefix.GeneralBorrowReadRowRange

namespace DuplicatePrefix.GeneralBorrowFreshReadRegistration
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A fresh protector changes no old node's held flag. Exact Read normal data
and both full finite-mask callback authorizations survive unchanged. -/
theorem row (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (tag : BorTag) (kind : ProtectorKind) (fresh : GeneralBorrowProtector.Fresh tree tag)
    (source selected : Option UniIndex) (maximum : Option BorTag)
    (old : GeneralBorrowReadRowNormal.ReadRow tree location protections source selected maximum) :
    Nonempty (GeneralBorrowReadRowNormal.ReadRow tree location (protections.insert tag kind) source selected maximum) := by
  have same : ∀ index node,tree.nodeAt index = some node →
      (protections.insert tag kind).contains node.tag = protections.contains node.tag := by
    intro index node present
    exact ProtectorInsertion.contains_other protections tag node.tag kind (fresh (index,node)
      (Array.mem_toList_iff.mp ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present)))
  have projection := GeneralBorrowProtector.normal_projection tree location protections tag kind fresh
  refine ⟨{wildcard := old.wildcard,rootPath := ?_,rootPresent := old.rootPresent,cutoff := old.cutoff,normal := ?_,callbacks := ?_}⟩
  · intro anchor present
    rw [projection]
    exact old.rootPath anchor present
  · intro anchor present
    obtain ⟨normal⟩ := old.normal anchor present
    refine ⟨{component := normal.component,permissions := ?_}⟩
    intro index included valid
    rw [projection]
    exact normal.permissions index included valid
  · intro position valid different
    obtain ⟨support,read,write⟩ := old.callbacks position valid different
    exact ⟨support,GeneralBorrowFreshRegistration.authorization tree location protections _ same _ _ _ _ support read,
      GeneralBorrowFreshRegistration.authorization tree location protections _ same _ _ _ _ support write⟩

/-- The internal Read owner window is retained on the same tree and byte range;
registration creates no Write normal premise for a shared source. -/
theorem positive (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (kind : ProtectorKind)
    (fresh : GeneralBorrowProtector.Fresh tree tag) (anchor selected : UniIndex)
    (maximum : Option BorTag) (offset len : UInt64)
    (old : GeneralBorrowReadRowRange.Positive tree protections anchor selected maximum offset len) :
    Nonempty (GeneralBorrowReadRowRange.Positive tree (protections.insert tag kind) anchor selected maximum offset len) := by
  refine ⟨{positive := old.positive,bounds := old.bounds,sourcePresent := old.sourcePresent,rows := ?_}⟩
  intro position valid nonzero before after
  obtain ⟨oldRow⟩ := old.rows position valid nonzero before after
  exact row tree _ protections tag kind fresh (some anchor) (some selected) maximum oldRow

end DuplicatePrefix.GeneralBorrowFreshReadRegistration
