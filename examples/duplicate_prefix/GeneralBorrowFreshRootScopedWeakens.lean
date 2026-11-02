import duplicate_prefix.GeneralBorrowFreshRootScopedReadRow
import duplicate_prefix.GeneralBorrowReadProtectorRowWeakens
import duplicate_prefix.GeneralBorrowHiddenProtectorRowWeakens
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedWeakens
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
theorem row (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (weaken : ∀ tag,after.contains tag = true → before.contains tag = true)
    (same : ∀ index node,tree.nodeAt index = some node → node.isExposed = true → after.contains node.tag = before.contains node.tag)
    (source selected : UniIndex) (maximum : BorTag)
    (old : GeneralBorrowFreshRootScopedRow.Row tree location before source selected maximum) :
    Nonempty (GeneralBorrowFreshRootScopedRow.Row tree location after source selected maximum) := by
  obtain ⟨base⟩ := GeneralBorrowHiddenProtectorRowWeakens.row tree location before after weaken same (some source) (some selected) (some maximum) old.base
  refine ⟨⟨base,old.exposed,?_⟩⟩
  intro position valid different
  obtain ⟨support,bounded,read,write⟩ := old.callbacks position valid different
  exact ⟨support,bounded,GeneralBorrowHiddenProtectorRowWeakens.authorization tree location before after weaken same _ _ _ _ _ read,
    GeneralBorrowHiddenProtectorRowWeakens.authorization tree location before after weaken same _ _ _ _ _ write⟩

theorem positive (tree : BorrowTree) (before after : ProtectedTags)
    (weaken : ∀ tag,after.contains tag = true → before.contains tag = true)
    (same : ∀ index node,tree.nodeAt index = some node → node.isExposed = true → after.contains node.tag = before.contains node.tag)
    (source selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (old : GeneralBorrowFreshRootScopedRow.Positive tree before source selected maximum offset len) :
    Nonempty (GeneralBorrowFreshRootScopedRow.Positive tree after source selected maximum offset len) := by
  obtain ⟨base⟩ := GeneralBorrowHiddenProtectorRowWeakens.positive tree before after weaken same (some source) (some selected) (some maximum) offset len old.base
  refine ⟨⟨base,?_⟩⟩
  intro position valid nonzero start stop
  obtain ⟨oldRow⟩ := old.rows position valid nonzero start stop
  exact row tree _ before after weaken same source selected maximum oldRow

theorem read_row (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (weaken : ∀ tag,after.contains tag = true → before.contains tag = true)
    (same : ∀ index node,tree.nodeAt index = some node → node.isExposed = true → after.contains node.tag = before.contains node.tag)
    (source selected : UniIndex) (maximum : BorTag)
    (old : GeneralBorrowFreshRootScopedReadRow.Row tree location before source selected maximum) :
    Nonempty (GeneralBorrowFreshRootScopedReadRow.Row tree location after source selected maximum) := by
  obtain ⟨base⟩ := GeneralBorrowReadProtectorRowWeakens.row tree location before after weaken same (some source) (some selected) (some maximum) old.base
  refine ⟨⟨base,old.exposed,?_⟩⟩
  intro position valid different
  obtain ⟨support,bounded,read,write⟩ := old.callbacks position valid different
  exact ⟨support,bounded,GeneralBorrowReadProtectorRowWeakens.authorization tree location before after weaken same _ _ _ _ _ read,
    GeneralBorrowReadProtectorRowWeakens.authorization tree location before after weaken same _ _ _ _ _ write⟩

theorem read_positive (tree : BorrowTree) (before after : ProtectedTags)
    (weaken : ∀ tag,after.contains tag = true → before.contains tag = true)
    (same : ∀ index node,tree.nodeAt index = some node → node.isExposed = true → after.contains node.tag = before.contains node.tag)
    (source selected : UniIndex) (maximum : BorTag) (offset len : UInt64)
    (old : GeneralBorrowFreshRootScopedReadRow.Positive tree before source selected maximum offset len) :
    Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive tree after source selected maximum offset len) := by
  obtain ⟨base⟩ := GeneralBorrowReadProtectorRowWeakens.positive tree before after weaken same source selected (some maximum) offset len old.base
  refine ⟨⟨base,?_⟩⟩
  intro position valid nonzero start stop
  obtain ⟨oldRow⟩ := old.rows position valid nonzero start stop
  exact read_row tree _ before after weaken same source selected maximum oldRow

end DuplicatePrefix.GeneralBorrowFreshRootScopedWeakens
