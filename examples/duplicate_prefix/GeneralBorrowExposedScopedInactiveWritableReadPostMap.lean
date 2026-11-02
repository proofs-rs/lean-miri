import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadData
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableReadPostMap
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
private theorem nonempty_iff (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat→Prop) (writable : Nat→Bool) :
    Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location protections anchor selected head tail support writable) ↔
      Nonempty (GeneralBorrowExposedScopedInactiveMixedRangeData.Data tree location protections anchor selected head tail support writable) ∧
      tree.nodes.size<65536 ∧
      (∀index,area.support index→∃node,tree.nodeAt index=some node ∧node.children=#[] ∧node.isExposed=true) ∧
      (∀index node,area.support index→tree.nodeAt index=some node→
        GeneralBorrowExposedConditionalWritePermissions.Compatible (GeneralBorrowWildcardVirtualLeaf.effective location index node)
          .LocalAccess (protections.contains node.tag)) := by
  constructor
  · rintro ⟨data⟩;exact ⟨⟨data.base⟩,data.short,data.leaves,data.writableLeaves⟩
  · rintro ⟨⟨base⟩,short,leaves,writableLeaves⟩;exact ⟨⟨base,short,leaves,writableLeaves⟩⟩
/-- Replacing the allocation range map leaves every local scoped certificate
unchanged; the actual range loop retains its own row/geometry proof. -/
theorem post_map (tree : BorrowTree) (map : DedupRangeMap LocationTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat→Prop) (writable : Nat→Bool) :
    Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data {tree with locations:=map} location protections anchor selected head tail support writable)=
      Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location protections anchor selected head tail support writable) := by
  apply propext
  rw [nonempty_iff,nonempty_iff,GeneralBorrowExposedScopedInactiveMixedClosedData.post_map]
  rfl
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableReadPostMap
