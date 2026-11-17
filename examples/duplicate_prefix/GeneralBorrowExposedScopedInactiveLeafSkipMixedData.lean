import duplicate_prefix.GeneralBorrowExposedScopedInactiveMixedRangeData
import duplicate_prefix.GeneralBorrowExposedScopedInactiveLeafSkipData
import duplicate_prefix.GeneralBorrowExposedScopedInactiveLeafSkipMixedAccess
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveLeafSkipMixedData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowExposedKnownRootState
open GeneralBorrowExposedScopedInactiveMixedRangeData (Data Post)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex)  (range : ByteRange)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (support : Nat → Prop) (writable : Nat → Bool) (fits : tree.nodes.data.size ≤ 4294967296)
    (leaf : context.anchorNode.children=#[]) (hidden : context.anchorNode.isExposed=false)
    (data : Data tree location protections anchor selected head tail support writable) :
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections .SkipChildrenOfAccessed range) = none ∧
      Post tree (source_access_location (source_tree_access_at tree location (some anchor) .Read protections .SkipChildrenOfAccessed range)) protections anchor support writable := by
  have base := GeneralBorrowExposedScopedInactiveLeafSkipData.access tree location protections anchor selected head tail support range context leaf hidden data.base
  have callback := GeneralBorrowExposedScopedInactiveLeafSkipReadFrame.access tree location protections anchor selected head context.anchorNode context.selectedNode tail
    range context.roots data.base.forest data.base.component data.base.owned context.depth context.children context.anchorPresent context.selectedPresent leaf hidden
    data.base.rootPath data.base.ancestors data.base.separate data.base.coherent data.base.readable context.tags data.base.primary data.base.virtual
  have mixed : GeneralBorrowExposedScopedOwnership.Pointwise data.base.component.support
      (source_normal_projection tree location protections) writable
      (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat) := by
    rw [data.support_eq]
    exact data.mixed
  obtain ⟨after,actual,status,preserved⟩ := GeneralBorrowExposedScopedInactiveLeafSkipMixedAccess.mixed tree location protections
    anchor selected head context.anchorNode context.selectedNode tail range context.roots data.base.forest data.base.component data.base.owned
    context.depth context.children context.anchorPresent context.selectedPresent leaf hidden data.base.rootPath data.base.ancestors data.base.separate
    data.base.coherent data.base.readable context.tags data.base.primary fits writable mixed data.base.virtual
  refine ⟨base.1,?_,?_,base.2,?_⟩
  · rw [callback.choose_spec.1]
    exact callback.choose_spec.2.2.2.2.1
  · rw [callback.choose_spec.1]
    exact callback.choose_spec.2.2.2.1
  · rw [actual]
    rw [data.support_eq] at preserved
    exact preserved

end DuplicatePrefix.GeneralBorrowExposedScopedInactiveLeafSkipMixedData
