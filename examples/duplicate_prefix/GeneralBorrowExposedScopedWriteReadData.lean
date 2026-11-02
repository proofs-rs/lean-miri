import duplicate_prefix.GeneralBorrowExposedScopedLeafSeed
import duplicate_prefix.GeneralBorrowExposedScopedUniqueReadData
namespace DuplicatePrefix.GeneralBorrowExposedScopedWriteReadData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Restored scoped Write ownership also supplies the target Read callback.
Actual retained Unique leaf rows reconstruct the Read count/profile witnesses;
no implication between arbitrary Write and Read cache profiles is assumed. -/
noncomputable def read (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (data : GeneralBorrowExposedKnownRootRangeData.Data tree location protections anchor selected head tail .Write)
    (short : tree.nodes.size<65536)
    (leaves : ∀ index,area.support index → ∃ node,tree.nodeAt index=some node ∧ node.children=#[] ∧ node.isExposed=true)
    (unique : ∀ index,area.support index → location.perms.get index=some GeneralBorrowWildcardLeaf.unique)
    (first : head≠selected → area.support head) (rest : ∀ root∈tail,root≠selected → area.support root) :
    GeneralBorrowExposedKnownRootRangeData.Data tree location protections anchor selected head tail .Read := by
  have mixed : GeneralBorrowExposedScopedMixedRangeData.Mixed tree location protections anchor data.component.support (fun _=>true) := by
    intro position supported bound
    have size : (source_normal_projection tree location protections).locationStates.size=(source_normal_projection tree location protections).topology.nodes.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_mapIdx,Array.size_map]
    obtain ⟨state,present,permission⟩:=data.owned position supported (by rw [←size];exact bound)
    exact ⟨state,present,by simpa only [GeneralBorrowPermissions.Required,GeneralBorrowPermissions.AccessOwned,Bool.true_eq,ite_true] using permission⟩
  have result:=GeneralBorrowExposedScopedLeafSeed.seed tree location protections anchor selected head tail data.component.support (fun _=>true)
    context data.forest data.component rfl mixed data.rootPath data.hidden data.separate data.coherent short (by
      intro index included
      obtain ⟨node,present,leaf,exposed⟩:=leaves index included
      refine ⟨node,present,leaf,exposed,?_,?_⟩
      · simp [GeneralBorrowExposureCardinality.effective,unique index included,GeneralBorrowWildcardLeaf.unique,Permission.strongestAllowedLocalAccess,
          GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsRead]
      · simp [GeneralBorrowWildcardVirtualLeaf.effective,unique index included,GeneralBorrowWildcardLeaf.unique,LocationState.possible]) first rest
  exact result.base
end DuplicatePrefix.GeneralBorrowExposedScopedWriteReadData
