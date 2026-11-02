import duplicate_prefix.S05SemanticReadDFS
import duplicate_prefix.GeneralBorrowWildcardTaskRegions

namespace DuplicatePrefix.S05ReadPostorderGraph
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardSubtreeStack
open GeneralBorrowWildcardTaskRegions GeneralBorrowProjection
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Physical ancestor paths are comparable because each node has one parent. -/
theorem comparable {tree : BorrowTree} {left right witness : UniIndex}
    (first : Path tree left witness) (second : Path tree right witness) :
    Path tree left right ∨ Path tree right left := by
  induction first generalizing right with
  | refl node present => exact .inr second
  | @step parent child earlier node present edge ih =>
    cases second with
    | refl otherNode otherPresent => exact .inl (.step earlier node present edge)
    | @step otherParent _ previous otherNode otherPresent otherEdge =>
      have sameNode := Option.some.inj (present.symm.trans otherPresent)
      subst otherNode
      have sameParent := Option.some.inj (edge.symm.trans otherEdge)
      subst otherParent
      exact ih previous

theorem trans {tree : BorrowTree} {root middle last : UniIndex}
    (first : Path tree root middle) (second : Path tree middle last) : Path tree root last := by
  induction second with
  | refl => exact first
  | step earlier node present edge ih => exact .step ih node present edge

/-- A pending posttask has no earlier task whose root is its descendant.
Together with disjoint task regions this expresses the actual postorder
frontier; numeric work ranks alone do not express it. -/
def Separated (tree : BorrowTree) (stack : Array Task) : Prop :=
  stack.toList.Pairwise (fun earlier later => later.2 = true → ¬ Path tree later.1 earlier.1)

theorem initial (tree : BorrowTree) (root : UniIndex) : Separated tree #[(root,false)] := by
  simp [Separated]

theorem pop (tree : BorrowTree) (stack : Array Task) (task : Task)
    (separated : Separated tree (stack.push task)) : Separated tree stack := by
  exact (List.pairwise_append.mp (by simpa only [Separated,Array.toList_push] using separated)).1

private theorem apart_top (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (stack : Array Task) (top earlier : Task) (member : earlier ∈ stack.toList)
    (disjoint : Disjoint (source_normal_projection tree location protections).topology (stack.push top)) :
    Apart (source_normal_projection tree location protections).topology earlier top := by
  have all := (List.pairwise_append.mp (by simpa only [Disjoint,Array.toList_push] using disjoint)).2.2
  exact all earlier member top (by simp)

theorem expand (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (stack : Array Task) (index : UniIndex) (node : TreeNode)
    (separated : Separated tree (stack.push (index,false)))
    (disjoint : Disjoint (source_normal_projection tree location protections).topology (stack.push (index,false))) :
    Separated tree (expanded stack index node.children) := by
  have previous := pop tree stack (index,false) separated
  unfold Separated expanded
  rw [Array.toList_append,Array.toList_push,Array.toList_map]
  apply List.pairwise_append.mpr
  refine ⟨?_,?_,?_⟩
  · rw [List.pairwise_append]
    refine ⟨previous,by simp,?_⟩
    intro earlier member later last laterPost path
    have same : later = (index,true) := by simpa using last
    subst later
    have apart := apart_top tree location protections stack (index,false) earlier member disjoint
    have desc := GeneralBorrowPhysicalRootPath.projection_desc tree location protections index earlier.1 path
    have own : Region (source_normal_projection tree location protections).topology earlier earlier.1.toNat := by
      cases h : earlier.2
      · simpa only [Region,h,Bool.false_eq_true,ite_false] using GeneralBorrowForest.Desc.refl earlier.1.toNat desc.valid.2
      · simp [Region,h]
    exact apart earlier.1.toNat ⟨own,desc⟩
  · apply List.pairwise_map.mpr
    exact List.pairwise_of_forall (by intro first second impossible; cases impossible)
  · intro earlier member later laterMember laterPost
    obtain ⟨child,childMember,equal⟩ := List.mem_map.mp laterMember
    subst later
    cases laterPost

/-- At the top postvisit, a strict descendant's processed-or-pending
certificate must already be discharged: no remaining task can reach it. -/
theorem frontier (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (stack : Array Task) (index witness : UniIndex) (seen : Bool)
    (path : Path tree index witness) (different : witness ≠ index)
    (separated : Separated tree (stack.push (index,true)))
    (disjoint : Disjoint (source_normal_projection tree location protections).topology (stack.push (index,true)))
    (pending : GeneralBorrowWildcardControlWitness.Pending tree witness seen (stack.push (index,true))) : seen = true := by
  rcases pending with ready | ⟨task,member,taskPath,last⟩
  · exact ready
  · simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with earlier | equal
    · have separatedTop := (List.pairwise_append.mp (by simpa only [Separated,Array.toList_push] using separated)).2.2
      have outside : ¬ Path tree index task.1 := separatedTop task earlier (index,true) (by simp) rfl
      cases taskPost : task.2 with
      | true =>
        have same := last taskPost
        rw [same] at outside
        exact False.elim (outside path)
      | false =>
        rcases comparable path taskPath with toTask | toIndex
        · exact False.elim (outside toTask)
        · have apart := apart_top tree location protections stack (index,true) task earlier disjoint
          have desc := GeneralBorrowPhysicalRootPath.projection_desc tree location protections task.1 index toIndex
          exact False.elim (apart index.toNat ⟨by simpa only [Region,taskPost,Bool.false_eq_true,ite_false] using desc,by simp [Region]⟩)
    · subst task
      exact False.elim (different (last rfl).symm)

end DuplicatePrefix.S05ReadPostorderGraph
open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S05ReadPostorderGraph.comparable,
      ``DuplicatePrefix.S05ReadPostorderGraph.trans,
      ``DuplicatePrefix.S05ReadPostorderGraph.expand,
      ``DuplicatePrefix.S05ReadPostorderGraph.frontier] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
