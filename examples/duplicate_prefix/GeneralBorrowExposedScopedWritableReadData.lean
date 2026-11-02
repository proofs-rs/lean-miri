import duplicate_prefix.GeneralBorrowExposedScopedWritableLeafWriteSeed
import duplicate_prefix.GeneralBorrowExposedScopedLeafWriteReadClosed
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableReadData
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- Mixed hidden-component data and genuinely writable effective old leaves.
Lazy defaults remain lazy until the actual operation visits them. -/
structure Data (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat→Prop) (writable : Nat→Bool) where
  base : GeneralBorrowExposedScopedMixedRangeData.Data tree location protections anchor selected head tail support writable
  short : tree.nodes.size<65536
  leaves : ∀index,area.support index→∃node,tree.nodeAt index=some node ∧node.children=#[] ∧node.isExposed=true
  writableLeaves : ∀index node,area.support index→tree.nodeAt index=some node→
    GeneralBorrowExposedConditionalWritePermissions.Compatible (GeneralBorrowWildcardVirtualLeaf.effective location index node)
      .LocalAccess (protections.contains node.tag)

noncomputable def write (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat→Prop)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (data : Data tree location protections anchor selected head tail support (fun _=>true)) :
    GeneralBorrowExposedKnownRootRangeData.Data tree location protections anchor selected head tail .Write :=
  GeneralBorrowExposedScopedWritableLeafWriteSeed.seed tree location protections anchor selected head tail support context
    data.base.base.forest data.base.base.component data.base.support_eq data.base.mixed data.base.base.rootPath
    data.base.base.hidden data.base.base.separate data.base.base.coherent data.short
    (by intro index included;obtain ⟨node,present,leaf,exposed⟩:=data.leaves index included
        exact ⟨node,present,leaf,exposed,data.writableLeaves index node included present⟩)
    (by intro different;let primary:=data.base.base.primary different;exact primary.base.included head primary.base.rooted)
    (by intro root member different;let virtual:=data.base.base.virtual root member different;exact virtual.included root virtual.rooted)

noncomputable def strong (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat→Prop)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (data : Data tree location protections anchor selected head tail support (fun _=>true)) :
    GeneralBorrowExposedScopedLeafWriteReadClosed.Data tree location protections anchor selected head tail := by
  refine ⟨write tree location protections anchor selected head tail support context data,data.short,data.leaves,?_⟩
  intro index included
  obtain ⟨node,present,leaf,exposed⟩:=data.leaves index included
  exact GeneralBorrowExposureCardinality.exposed_self location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location protections) data.base.base.coherent data.short index node present exposed .Write
    (GeneralBorrowExposedScopedWritableLeafWriteData.support location protections index node (data.writableLeaves index node included present))
end DuplicatePrefix.GeneralBorrowExposedScopedWritableReadData
