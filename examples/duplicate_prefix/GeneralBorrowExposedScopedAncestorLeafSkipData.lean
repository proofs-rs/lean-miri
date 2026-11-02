import duplicate_prefix.GeneralBorrowExposedScopedAncestorRangeData
import duplicate_prefix.GeneralBorrowExposedScopedAncestorLeafSkipReadFrame
namespace DuplicatePrefix.GeneralBorrowExposedScopedAncestorLeafSkipData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowExposedKnownRootState
open GeneralBorrowExposedKnownRootRangeData (Context)
open GeneralBorrowExposedScopedAncestorRangeData (Data)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Initial exposed-ancestor component data supplies the actual concrete Read
and retains its Unique permissions after every other-root callback. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) (range : ByteRange)
    (context : Context tree anchor selected head tail)
    (leaf : context.anchorNode.children=#[]) (hidden : context.anchorNode.isExposed=false)
    (data : Data tree location protections anchor selected head tail support) :
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections .SkipChildrenOfAccessed range)=none ∧
    GeneralBorrowExposedConstructorUnique.Unique tree
      (source_access_location (source_tree_access_at tree location (some anchor) .Read protections .SkipChildrenOfAccessed range)) support := by
  obtain ⟨after,actual,status,_,_,_,keep⟩ := GeneralBorrowExposedScopedAncestorLeafSkipReadFrame.access tree location protections
    anchor selected head context.anchorNode context.selectedNode tail range context.roots data.forest data.component data.owned
    context.depth context.children context.anchorPresent context.selectedPresent leaf hidden data.rootPath data.ancestors data.separate
    data.coherent data.readable context.tags data.primary data.virtual
  refine ⟨status,?_⟩
  rw [actual]
  intro query node member present exposed
  have supported : data.component.support query.toNat := by rw [data.supportEq];exact member
  have outside : ¬area.support query := by intro inside;exact data.separate query inside supported
  have slot := keep query outside
  have finalPresent : tree.locationStateAt (tree.performNormalAccessAt location anchor .Read protections .SkipChildrenOfAccessed).location query=
      some ((after.perms.get query).getD node.defaultLocationState) := by
    simp only [BorrowTree.locationStateAt,present,bind,pure,Option.bind_some,slot]
  exact (GeneralBorrowExposedScopedAncestorPermission.preserves tree location protections anchor .Read .SkipChildrenOfAccessed
    data.forest data.component data.owned context.depth context.children context.anchorNode context.anchorPresent data.ancestors
    query node _ supported present exposed finalPresent).2
end DuplicatePrefix.GeneralBorrowExposedScopedAncestorLeafSkipData
