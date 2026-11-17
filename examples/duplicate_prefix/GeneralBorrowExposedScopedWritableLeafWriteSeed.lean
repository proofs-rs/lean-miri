import duplicate_prefix.GeneralBorrowExposedScopedWritableLeafWriteData
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableLeafWriteSeed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedMixedRangeData (Mixed)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Assemble an initial Write contract from raw graph/component ownership and
exposed supporting leaf resources. No per-root call result is an input. -/
noncomputable def seed (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat)
    (supportEq : component.support = support) (mixed : Mixed tree location protections anchor support (fun _=>true))
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = selected.toNat)
    (hidden : ∀ index node,component.support index.toNat → tree.nodeAt index = some node → node.isExposed = false)
    (separate : ∀ index,area.support index → ¬component.support index.toNat)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (leafs : ∀ index,area.support index → ∃ node,tree.nodes.get index = some node ∧ node.children = #[] ∧
      node.isExposed = true ∧
      GeneralBorrowExposedConditionalWritePermissions.Compatible (GeneralBorrowWildcardVirtualLeaf.effective location index node) .LocalAccess (protections.contains node.tag))
    (first : head ≠ selected → area.support head)
    (rest : ∀ root ∈ tail,root ≠ selected → area.support root) :
    GeneralBorrowExposedKnownRootRangeData.Data tree location protections anchor selected head tail .Write := by
  have profile := GeneralBorrowExposedScopedWritableLeafWriteData.profile tree location protections coherent short (by
    intro index node included present
    obtain ⟨actual,found,leaf,exposed,unique⟩:=leafs index included
    have same:=Option.some.inj (found.symm.trans present)
    subst node
    exact ⟨exposed,unique⟩)
  refine {
    forest := forest
    component := component
    owned := ?_
    rootPath := rootPath
    hidden := hidden
    separate := separate
    coherent := coherent
    profile := profile
    primary := ?_
    virtual := ?_ }
  · intro index included valid
    have size : (source_normal_projection tree location protections).locationStates.size =
        (source_normal_projection tree location protections).topology.nodes.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_mapIdx,Array.size_map]
    obtain ⟨state,present,permission⟩ := mixed index (by rw [←supportEq];exact included) (by rw [size];exact valid)
    exact ⟨state,present,(by simpa only [GeneralBorrowPermissions.Required,GeneralBorrowPermissions.AccessOwned,Bool.true_eq,ite_true] using permission)⟩
  · intro different
    let node := Classical.choose (leafs head (first different))
    have facts := Classical.choose_spec (leafs head (first different))
    rcases facts with ⟨present,leaf,exposed,unique⟩
    exact GeneralBorrowExposedScopedWritableLeafWriteData.primary tree location protections head node present leaf (first different)
      exposed unique coherent short context.depth profile
      (GeneralBorrowExposedScopedReciprocal.of_forest tree location protections forest context.depth)
  · intro root member different
    let node := Classical.choose (leafs root (rest root member different))
    have facts := Classical.choose_spec (leafs root (rest root member different))
    rcases facts with ⟨present,leaf,exposed,unique⟩
    exact GeneralBorrowExposedScopedLeafWriteData.virtual tree location protections root node present leaf (rest root member different)
      coherent short context.depth profile
end DuplicatePrefix.GeneralBorrowExposedScopedWritableLeafWriteSeed
