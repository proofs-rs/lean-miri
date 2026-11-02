import duplicate_prefix.GeneralBorrowWildcardControlStack
import duplicate_prefix.GeneralBorrowPhysicalRootPath
namespace DuplicatePrefix.GeneralBorrowWildcardTaskRegions
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForest GeneralBorrowWildcardSubtreeStack GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

def Region (tree : TraversalTree) (task : Task) (query : Nat) : Prop :=
  if task.2 then query = task.1.toNat else Desc tree task.1.toNat query

def Apart (tree : TraversalTree) (left right : Task) : Prop :=
  ∀ query, ¬ (Region tree left query ∧ Region tree right query)

def Disjoint (tree : TraversalTree) (stack : Array Task) : Prop := stack.toList.Pairwise (Apart tree)

theorem initial (tree : TraversalTree) (root : UniIndex) : Disjoint tree #[(root,false)] := by
  simp [Disjoint]

theorem pop (tree : TraversalTree) (stack : Array Task) (task : Task)
    (valid : Disjoint tree (stack.push task)) : Disjoint tree stack := by
  exact (List.pairwise_append.mp (by simpa only [Disjoint,Array.toList_push] using valid)).1

/-- Every new task produced by the literal child-push expansion lies within
the former previsit region. This is independent of permission state. -/
theorem expanded_subset (tree : TraversalTree) (forest : Forest tree)
    (index : UniIndex) (children : Array UniIndex) (valid : index.toNat < tree.nodes.size)
    (shape : tree.nodes[index.toNat].children = children.toList.map UniIndex.toNat)
    (task : Task) (member : task ∈ ((#[(index,true)] : Array Task) ++ children.map (fun child => (child,false))).toList)
    (query : Nat) (inside : Region tree task query) : Region tree (index,false) query := by
  simp only [Array.toList_append,Array.toList_map,List.mem_append] at member
  rcases member with parent | inChildren
  · have same : task = (index,true) := by simpa using parent
    subst task
    simp only [Region,ite_true,ite_false] at inside ⊢
    rw [inside]
    exact .refl index.toNat valid
  · obtain ⟨childIndex,childMember,same⟩ := List.mem_map.mp inChildren
    subst task
    have edge := forest.childParent index.toNat valid childIndex.toNat (by rw [shape];exact List.mem_map.mpr ⟨childIndex,childMember,rfl⟩)
    exact (Desc.step (Desc.refl index.toNat valid) edge.1 edge.2).trans inside

theorem expanded_internal (tree : TraversalTree) (forest : Forest tree)
    (index : UniIndex) (children : Array UniIndex) (valid : index.toNat < tree.nodes.size)
    (shape : tree.nodes[index.toNat].children = children.toList.map UniIndex.toNat) :
    Disjoint tree ((#[(index,true)] : Array Task) ++ children.map (fun child => (child,false))) := by
  simp only [Disjoint,Array.toList_append,Array.toList_map]
  change ([(index,true)] ++ (children.toList.map (fun child => (child,false)))).Pairwise (Apart tree)
  apply List.pairwise_append.mpr
  refine ⟨by simp,?_,?_⟩
  · apply List.pairwise_map.mpr
    have distinct : children.toList.Pairwise (fun left right => left.toNat ≠ right.toNat) := by
      apply List.pairwise_map.mp
      rw [←shape]
      exact forest.childrenDistinct index.toNat valid
    apply distinct.imp_of_mem
    intro left right leftMember rightMember different query both
    exact siblings_disjoint forest index.toNat left.toNat right.toNat query valid
      (by rw [shape];exact List.mem_map.mpr ⟨left,leftMember,rfl⟩)
      (by rw [shape];exact List.mem_map.mpr ⟨right,rightMember,rfl⟩) different both
  · intro parent parentMember child childMember query both
    have parentEq : parent = (index,true) := by simpa using parentMember
    subst parent
    obtain ⟨childIndex,member,same⟩ := List.mem_map.mp childMember
    subst child
    have edge := forest.childParent index.toNat valid childIndex.toNat
      (by rw [shape];exact List.mem_map.mpr ⟨childIndex,member,rfl⟩)
    have rank := both.2.rank_le forest
    change forest.rank childIndex.toNat ≤ forest.rank query at rank
    have above := (forest.parents childIndex.toNat edge.1 index.toNat edge.2).2
    have same : query = index.toNat := both.1
    rw [same] at rank
    omega

/-- Literal expansion preserves pairwise disjoint unprocessed regions. -/
theorem expand (tree : TraversalTree) (forest : Forest tree)
    (stack : Array Task) (index : UniIndex) (children : Array UniIndex) (valid : index.toNat < tree.nodes.size)
    (shape : tree.nodes[index.toNat].children = children.toList.map UniIndex.toNat)
    (disjoint : Disjoint tree (stack.push (index,false))) :
    Disjoint tree (expanded stack index children) := by
  have old : stack.toList.Pairwise (Apart tree) ∧ ([(index,false)] : List Task).Pairwise (Apart tree) ∧
      ∀ left ∈ stack.toList, ∀ right ∈ [(index,false)], Apart tree left right := by
    apply List.pairwise_append.mp
    simpa only [Disjoint,Array.toList_push] using disjoint
  simp only [Disjoint,expanded,Array.toList_append,Array.toList_push,Array.toList_map]
  change ((stack.toList ++ [(index,true)]) ++ (children.toList.map (fun child => (child,false)))).Pairwise (Apart tree)
  rw [List.append_assoc]
  apply List.pairwise_append.mpr
  refine ⟨old.1,by simpa only [Disjoint,Array.toList_append,Array.toList_map] using expanded_internal tree forest index children valid shape,?_⟩
  intro left leftMember right rightMember query both
  exact old.2.2 left leftMember (index,false) (by simp) query
    ⟨both.1,expanded_subset tree forest index children valid shape right (by simpa using rightMember) query both.2⟩

end DuplicatePrefix.GeneralBorrowWildcardTaskRegions
