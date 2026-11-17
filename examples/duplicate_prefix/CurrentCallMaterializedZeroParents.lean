import duplicate_prefix.CurrentCallEmptyMaterializedSourceFacts
import duplicate_prefix.CurrentCallSupportChain

namespace DuplicatePrefix.CurrentCallMaterializedZeroParents
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CurrentCallResourceNormalization GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem literal_order (tree : BorrowTree) (root child : TreeNode)
    (nodes : tree.nodes.data = #[some root,some child])
    (rootNone : root.parent=none)
    (childParent : child.parent=none ∨ child.parent=some ⟨0⟩)
    (older : root.tag.value≤child.tag.value) : ParentTagOrder tree := by
  intro index node present parent parentNode edge parentAt
  have valid:=GeneralBorrowNodeUpdate.lookup_valid _ _ _ present
  have bound : index.toNat<2 := by simpa [nodes] using valid
  have cases : index=⟨0⟩ ∨ index=⟨1⟩ := by
    rcases (by omega : index.toNat=0 ∨ index.toNat=1) with h|h
    · exact Or.inl (GeneralBorrowNodeUpdate.index_injective _ _ h)
    · exact Or.inr (GeneralBorrowNodeUpdate.index_injective _ _ h)
  rcases cases with rfl|rfl
  · have equal : node=root := by simpa [UniValMap.get,nodes,UniIndex.toNat] using present.symm
    subst node
    simp [rootNone] at edge
  · have equal : node=child := by simpa [UniValMap.get,nodes,UniIndex.toNat] using present.symm
    subst node
    rcases childParent with h|h
    · simp [h] at edge
    · have p : parent=⟨0⟩ := by simpa [h] using edge.symm
      subst parent
      have equal : parentNode=root := by simpa [UniValMap.get,nodes,UniIndex.toNat] using parentAt.symm
      subst parentNode
      exact older

theorem concrete (root tag : BorTag) (size : Size) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts (TypedRetagConcreteEmpty.lazyTree root tag size.bytes) global)
    (older : root.value<tag.value) :
    ∃ C, ParentInterpretation (TypedRetagConcreteEmpty.lazyTree root tag size.bytes) C := by
  let tree := TypedRetagConcreteEmpty.lazyTree root tag size.bytes
  let rootNode : TreeNode := { tag:=root,parent:=none,children:=#[⟨1⟩],defaultInitialPermission:=.Disabled,defaultInitialSifa:=.None }
  have atRoot : tree.nodes.get allocationRoot=some rootNode := rfl
  let chain : CurrentCallSupportChain.Chain tree allocationRoot := .root (.refl allocationRoot rootNode atRoot)
  refine ⟨chain.completion,chain.parents runtime.formed.toGraphState ?_ (by change ([allocationRoot] : List UniIndex).Nodup; simp) rootNode atRoot rfl⟩
  exact literal_order tree rootNode _ rfl rfl (Or.inr rfl) (Nat.le_of_lt older)

theorem wildcard (root tag : BorTag) (size : Size) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts (CurrentCallEmptyMaterializedWildcard.finalTree root tag size) global)
    (older : root.value<tag.value) :
    ∃ C, ParentInterpretation (CurrentCallEmptyMaterializedWildcard.finalTree root tag size) C := by
  let tree := CurrentCallEmptyMaterializedWildcard.finalTree root tag size
  let rootNode : TreeNode := { tag:=root,parent:=none,children:=#[],defaultInitialPermission:=.newDisabled,defaultInitialSifa:=.None }
  have atRoot : tree.nodes.get allocationRoot=some rootNode := rfl
  let chain : CurrentCallSupportChain.Chain tree allocationRoot := .root (.refl allocationRoot rootNode atRoot)
  refine ⟨chain.completion,chain.parents runtime.formed.toGraphState ?_ (by change ([allocationRoot,⟨1⟩] : List UniIndex).Nodup; decide) rootNode atRoot rfl⟩
  exact literal_order tree rootNode _ rfl rfl (Or.inl rfl) (Nat.le_of_lt older)
end DuplicatePrefix.CurrentCallMaterializedZeroParents

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "CurrentCallMaterializedZeroParents.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved zero-parent dependency {name}: {dependency}"
