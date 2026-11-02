import duplicate_prefix.GeneralBorrowForest

namespace DuplicatePrefix.GeneralBorrowForestWeights
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowForest
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Finite set enumeration of actual descendants, including the root itself.
No traversal execution or operation-success condition is part of this definition. -/
def descendants (tree : TraversalTree) (root : Nat) : List Nat := by
  classical
  exact (List.range tree.nodes.size).filter (fun index => decide (Desc tree root index))

def weight (tree : TraversalTree) (root : Nat) : Nat := (descendants tree root).length

theorem mem_descendants (tree : TraversalTree) (root index : Nat) :
    index ∈ descendants tree root ↔ index < tree.nodes.size ∧ Desc tree root index := by
  classical
  simp [descendants]

theorem descendants_distinct (tree : TraversalTree) (root : Nat) :
    (descendants tree root).Nodup := by
  classical
  exact List.nodup_range.filter _

/-- Every subtree has at most the physical topology's number of slots,
including sparse absent slots in that upper bound. -/
theorem bounded (tree : TraversalTree) (root : Nat) : weight tree root ≤ tree.nodes.size := by
  classical
  unfold weight descendants
  simpa only [List.length_range] using (List.length_filter_le (fun index => decide (Desc tree root index)) (List.range tree.nodes.size))

/-- Sibling descendant enumerations are disjoint by unique parents and rank;
adding the parent itself still produces a distinct list. -/
theorem child_union_distinct (tree : TraversalTree) (forest : Forest tree) (root : Nat)
    (valid : root < tree.nodes.size) :
    ((tree.nodes[root].children.flatMap (descendants tree)) ++ [root]).Nodup := by
  have distinctChildren := forest.childrenDistinct root valid
  apply List.nodup_append.mpr
  refine ⟨?_,by simp,?_⟩
  · apply List.pairwise_flatMap.mpr
    constructor
    · intro child member
      exact descendants_distinct tree child
    · apply distinctChildren.imp_of_mem
      intro left right leftMember rightMember different first inFirst second inSecond same
      have leftDesc := ((mem_descendants tree left first).mp inFirst).2
      have rightDesc := ((mem_descendants tree right second).mp inSecond).2
      exact siblings_disjoint forest root left right first valid leftMember rightMember different
        ⟨leftDesc,by rw [same];exact rightDesc⟩
  · intro descendant member last lastMember same
    have lastEq : last = root := by simpa using lastMember
    obtain ⟨child,childMember,inChild⟩ := List.mem_flatMap.mp member
    have childData := forest.childParent root valid child childMember
    have descendantData := (mem_descendants tree child descendant).mp inChild
    have lower := descendantData.2.rank_le forest
    have higher := (forest.parents child childData.1 root childData.2).2
    have sameRoot : descendant = root := same.trans lastEq
    rw [sameRoot] at lower
    omega

/-- Canonical finite subtree weights pay for one visit plus all child subtree
weights. Acyclicity, unique parents and distinct child edges are graph data;
there is no successful-operation premise. -/
theorem children (tree : TraversalTree) (forest : Forest tree) (root : Nat)
    (valid : root < tree.nodes.size) :
    1 + (tree.nodes[root].children.map (weight tree)).sum ≤ weight tree root := by
  have included : (tree.nodes[root].children.flatMap (descendants tree)) ++ [root] ⊆ descendants tree root := by
    intro index member
    apply (mem_descendants tree root index).mpr
    rcases List.mem_append.mp member with childDesc | self
    · obtain ⟨child,childMember,inChild⟩ := List.mem_flatMap.mp childDesc
      have data := (mem_descendants tree child index).mp inChild
      have childData := forest.childParent root valid child childMember
      exact ⟨data.1,(Desc.step (Desc.refl root valid) childData.1 childData.2).trans data.2⟩
    · have same : index = root := by simpa using self
      subst index
      exact ⟨valid,Desc.refl root valid⟩
  have lengthBound := (child_union_distinct tree forest root valid).length_le_of_subset included
  change 1 + (tree.nodes[root].children.map (fun child => (descendants tree child).length)).sum ≤ (descendants tree root).length
  simpa only [List.length_append,List.length_flatMap,List.length_singleton,Nat.add_comm] using lengthBound

end
end DuplicatePrefix.GeneralBorrowForestWeights
