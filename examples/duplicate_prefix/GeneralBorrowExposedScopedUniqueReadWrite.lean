import duplicate_prefix.GeneralBorrowExposedScopedUniqueReadData
import duplicate_prefix.GeneralBorrowExposedScopedLeafWriteSeed
namespace DuplicatePrefix.GeneralBorrowExposedScopedUniqueReadWrite
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- All-writable mixed ownership and retained exposed Unique leaves reconstruct
the complete next Write input after an actual Read or release callback. -/
noncomputable def write (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (data : GeneralBorrowExposedScopedUniqueReadData.Data tree location protections anchor selected head tail support (fun _=>true)) :
    GeneralBorrowExposedKnownRootRangeData.Data tree location protections anchor selected head tail .Write := by
  let base := data.base.base
  have leaves : ∀ query,area.support query → ∃ node,tree.nodes.get query=some node ∧ node.children=#[] ∧ node.isExposed=true ∧
      GeneralBorrowWildcardVirtualLeaf.effective location query node=GeneralBorrowWildcardLeaf.unique := by
    intro query included
    obtain ⟨node,present,leaf,exposed⟩ := data.leaves query included
    exact ⟨node,present,leaf,exposed,by simp only [GeneralBorrowWildcardVirtualLeaf.effective,data.unique query included,Option.getD_some]⟩
  have first : head≠selected → area.support head := fun different => (base.primary different).base.included head (base.primary different).base.rooted
  have rest : ∀ root∈tail,root≠selected → area.support root := by
    intro root member different
    exact (base.virtual root member different).included root (base.virtual root member different).rooted
  exact GeneralBorrowExposedScopedLeafWriteSeed.seed tree location protections anchor selected head tail support context
    base.forest base.component data.base.support_eq data.base.mixed base.rootPath base.hidden base.separate base.coherent
    data.short leaves first rest
end DuplicatePrefix.GeneralBorrowExposedScopedUniqueReadWrite
