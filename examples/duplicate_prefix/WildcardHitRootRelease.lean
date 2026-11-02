import duplicate_prefix.ActualWildcardHitReference
import duplicate_prefix.EmptyForestUnmaterializedRelease

namespace DuplicatePrefix.WildcardHitRootRelease
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshNode
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- The ROOT FnEntry protector created by a live empty wildcard HIT is genuinely
released without touching bytes or exposure caches. Vacant permission data is
an initial-state invariant, not a release-success premise. -/
theorem release (tree : BorrowTree) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (aligned : tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.mapping.size ≤ 4294967295)
    (clean : ∀ position (valid : position < tree.locations.entries.size),
      tree.locations.entries[position].data.perms.get ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩ = none)
    (protections : ProtectedTags) :
    let result := ActualWildcardHitReference.finalTree tree tag
    result.releaseProtector tag protections = ⟨result,.Released⟩ := by
  let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
  have atEnd : index.toNat = tree.nodes.data.size := by
    simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
    exact aligned
  have tagged : (ActualWildcardHitReference.finalTree tree tag).indexOfTag tag = some index := by
    exact GeneralBorrowTagMap.pushed_get_new tree.tagMapping tag fresh index tree.tagMapping.deassigned
  have present : (ActualWildcardHitReference.finalTree tree tag).nodeAt index =
      some (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) :=
    append_get_same tree.nodes index _ atEnd
  exact EmptyForestUnmaterializedRelease.release _ tag index _ tagged present rfl clean protections

end DuplicatePrefix.WildcardHitRootRelease
