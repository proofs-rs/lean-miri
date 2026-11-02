import duplicate_prefix.GeneralBorrowExposedScopedInactiveLeafReadFrame
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveUniqueReadData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

structure Data (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) (writable : Nat → Bool) where
  base : GeneralBorrowExposedScopedInactiveMixedRangeData.Data tree location protections anchor selected head tail support writable
  short : tree.nodes.size < 65536
  leaves : ∀ index,area.support index → ∃ node,tree.nodeAt index = some node ∧ node.children = #[] ∧ node.isExposed = true
  unique : ∀ index,area.support index → location.perms.get index = some GeneralBorrowWildcardLeaf.unique

theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex)  (range : ByteRange)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (support : Nat → Prop) (writable : Nat → Bool) (fits : tree.nodes.data.size ≤ 4294967296)
    (data : Data tree location protections anchor selected head tail support writable) :
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections .VisitChildrenOfAccessed range) = none ∧
      Nonempty (Data tree (source_access_location (source_tree_access_at tree location (some anchor) .Read protections .VisitChildrenOfAccessed range))
        protections anchor selected head tail support writable) := by
  have closed := GeneralBorrowExposedScopedInactiveMixedClosedData.access tree location protections anchor selected head tail range context support writable fits data.base
  obtain ⟨base⟩ := closed.2
  refine ⟨closed.1,⟨{base := base,short := data.short,leaves := data.leaves,unique := ?_}⟩⟩
  intro query included
  have actual := GeneralBorrowExposedScopedInactiveLeafReadFrame.normal_only tree location protections anchor selected head tail range context support writable data.base data.short (by
    intro index member
    obtain ⟨node,present,leaf,exposed⟩ := data.leaves index member
    exact ⟨node,present,leaf,exposed,data.unique index member⟩)
  rw [actual.1]
  obtain ⟨node,present,leaf,exposed⟩ := data.leaves query included
  have outside := GeneralBorrowExposedScopedNormalCache.outside tree location protections anchor .Read .VisitChildrenOfAccessed
    data.base.base.component query node present
    (data.base.base.separate query included)
  exact outside.trans (data.unique query included)

private theorem nonempty_iff (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) (writable : Nat → Bool) :
    Nonempty (Data tree location protections anchor selected head tail support writable) ↔
      Nonempty (GeneralBorrowExposedScopedInactiveMixedRangeData.Data tree location protections anchor selected head tail support writable) ∧
      tree.nodes.size < 65536 ∧
      (∀ index,area.support index → ∃ node,tree.nodeAt index = some node ∧ node.children = #[] ∧ node.isExposed = true) ∧
      (∀ index,area.support index → location.perms.get index = some GeneralBorrowWildcardLeaf.unique) := by
  constructor
  · rintro ⟨data⟩;exact ⟨⟨data.base⟩,data.short,data.leaves,data.unique⟩
  · rintro ⟨⟨base⟩,short,leaves,unique⟩;exact ⟨⟨base,short,leaves,unique⟩⟩

theorem post_map (tree : BorrowTree) (map : DedupRangeMap LocationTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) (writable : Nat → Bool) :
    Nonempty (Data {tree with locations := map} location protections anchor selected head tail support writable) =
      Nonempty (Data tree location protections anchor selected head tail support writable) := by
  apply propext
  rw [nonempty_iff,nonempty_iff,GeneralBorrowExposedScopedInactiveMixedClosedData.post_map]
  rfl
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveUniqueReadData
