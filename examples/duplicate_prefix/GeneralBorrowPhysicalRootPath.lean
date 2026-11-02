import duplicate_prefix.GeneralBorrowWildcardControlWitness
import duplicate_prefix.GeneralBorrowNormalComponentNormalization
namespace DuplicatePrefix.GeneralBorrowPhysicalRootPath
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowTopology GeneralBorrowPresence
open GeneralBorrowExposedNonleafPrimaryPath
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A physical present-node path maps to the source normal topology's Desc. -/
theorem projection_desc (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root index : UniIndex) (path : Path tree root index) :
    Desc (source_normal_projection tree location protections).topology root.toNat index.toNat := by
  induction path with
  | refl node present =>
    apply Desc.refl
    have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes _ node present
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using bounded
  | @step parent child earlier node present edge ih =>
    have bounded : child.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
      have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes child node present
      unfold_general_projection
      unfold_general_topology
      simpa only [Array.size_map] using bounded
    apply Desc.step ih bounded
    have projected := projection_topology_node tree location protections child.toNat child node rfl present
    simp only [Array.getElem?_eq_getElem bounded,Option.getD_some] at projected
    rw [projected]
    simp only [edge,Option.map_some]

/-- Every member of the actual finite ancestor list is a genuine ancestor,
without assuming that member is the chosen root or that traversal succeeded. -/
theorem ancestor_desc (tree : TraversalTree) (forest : Forest tree)
    (fuel current root : Nat) (valid : current < tree.nodes.size)
    (member : root ∈ sourceAncestorPath tree fuel current) : Desc tree root current := by
  induction fuel generalizing current with
  | zero =>
    rw [ancestor_zero] at member
    have same : root = current := by simpa using member
    subst root
    exact .refl current valid
  | succ fuel ih =>
    rw [ancestor_succ] at member
    have node : nodeData tree current = tree.nodes[current] := by
      simp only [nodeData,Array.getElem?_eq_getElem valid,Option.getD_some]
    rw [node] at member
    cases edge : tree.nodes[current].parent with
    | none =>
      simp only [edge,List.mem_singleton] at member
      subst root
      exact .refl current valid
    | some parent =>
      simp only [edge,List.mem_cons] at member
      rcases member with same | rest
      · subst root
        exact .refl current valid
      · have parentValid := (forest.parents current valid parent edge).1
        exact .step (ih parent parentValid rest) valid edge

/-- The S01 Row rootPath field identifies the physical selected component. -/
theorem selected_desc (tree : TraversalTree) (forest : Forest tree)
    (anchor selected : Nat) (valid : anchor < tree.nodes.size)
    (path : (tree.ancestorPath anchor).getLast? = some selected) : Desc tree selected anchor :=
  ancestor_desc tree forest tree.nodes.size anchor selected valid (List.mem_of_getLast? path)

end DuplicatePrefix.GeneralBorrowPhysicalRootPath
