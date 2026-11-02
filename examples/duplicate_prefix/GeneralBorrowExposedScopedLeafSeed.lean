import duplicate_prefix.GeneralBorrowExposedScopedLeafData
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal
namespace DuplicatePrefix.GeneralBorrowExposedScopedLeafSeed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState (Scope Readable)
open GeneralBorrowExposedScopedMixedRangeData (Data Mixed)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Assemble an initial Read contract from raw graph/component ownership and
exposed supporting leaf resources. No per-root call result is an input. -/
noncomputable def seed (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (support : Nat → Prop) (writable : Nat → Bool)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat)
    (supportEq : component.support = support) (mixed : Mixed tree location protections anchor support writable)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = selected.toNat)
    (hidden : ∀ index node,component.support index.toNat → tree.nodeAt index = some node → node.isExposed = false)
    (separate : ∀ index,area.support index → ¬component.support index.toNat)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (leafs : ∀ index,area.support index → ∃ node,tree.nodes.get index = some node ∧ node.children = #[] ∧
      node.isExposed = true ∧
      GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location protections index node) .Read = true ∧
      (GeneralBorrowWildcardVirtualLeaf.effective location index node).possible = true)
    (first : head ≠ selected → area.support head)
    (rest : ∀ root ∈ tail,root ≠ selected → area.support root) :
    Data tree location protections anchor selected head tail support writable := by
  have profile : Readable tree location protections := GeneralBorrowExposedScopedLeafData.readable tree location protections coherent short (by
    intro index node included present
    obtain ⟨actual,found,leaf,exposed,supported,possible⟩ := leafs index included
    have same := Option.some.inj (found.symm.trans present)
    subst node
    exact ⟨exposed,supported,possible⟩)
  refine {
    base := {
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
    support_eq := supportEq
    mixed := mixed }
  · intro index included valid
    have size : (source_normal_projection tree location protections).locationStates.size =
        (source_normal_projection tree location protections).topology.nodes.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_mapIdx,Array.size_map]
    obtain ⟨state,present,permission⟩ := mixed index (by rw [←supportEq];exact included) (by rw [size];exact valid)
    exact ⟨state,present,GeneralBorrowExposedScopedMixedRebase.required_read _ _ _ _ permission⟩
  · intro different
    let node := Classical.choose (leafs head (first different))
    have facts := Classical.choose_spec (leafs head (first different))
    rcases facts with ⟨present,leaf,exposed,supported,possible⟩
    exact GeneralBorrowExposedScopedLeafData.primary tree location protections head node present leaf (first different)
      exposed supported coherent short context.depth profile
      (GeneralBorrowExposedScopedReciprocal.of_forest tree location protections forest context.depth)
  · intro root member different
    let node := Classical.choose (leafs root (rest root member different))
    have facts := Classical.choose_spec (leafs root (rest root member different))
    rcases facts with ⟨present,leaf,exposed,supported,possible⟩
    exact GeneralBorrowExposedScopedLeafData.virtual tree location protections root node present leaf (rest root member different)
      coherent short context.depth profile
end DuplicatePrefix.GeneralBorrowExposedScopedLeafSeed
