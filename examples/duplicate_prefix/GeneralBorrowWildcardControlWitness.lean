import duplicate_prefix.GeneralBorrowWildcardControlStack
import duplicate_prefix.GeneralBorrowExposedNonleafPrimaryPath
namespace DuplicatePrefix.GeneralBorrowWildcardControlWitness
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardSubtreeStack GeneralBorrowExposedNonleafPrimaryPath
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Ancestor-walk coverage gives a real downward child-reachable path when
parent nodes exist. Reciprocal child edges are needed only when expanding it. -/
theorem path_of_walk (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (root index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (fuel : Nat) (member : root ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes fuel index) : Path tree root index := by
  induction fuel generalizing index node with
  | zero => simp [GeneralBorrowExposureAncestorFold.walk] at member
  | succ fuel ih =>
    simp only [GeneralBorrowExposureAncestorFold.walk,List.mem_cons] at member
    rcases member with same | earlier
    · subst root
      exact .refl index node present
    · rw [present] at earlier
      cases edge : node.parent with
      | none => simp [edge] at earlier
      | some parent =>
        simp only [edge] at earlier
        obtain ⟨parentNode,parentPresent,smaller⟩ := depth.parent index node present parent edge
        exact .step (ih parent parentNode parentPresent earlier) node present edge

theorem path_of_covers (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (root index : UniIndex) (node : TreeNode) (present : tree.nodes.get index = some node)
    (covered : GeneralBorrowExposureCardinality.Covers tree.nodes root index) : Path tree root index := by
  have own : index ∈ GeneralBorrowExposureAncestorFold.walk tree.nodes (tree.nodes.size+1) index := by
    simp [GeneralBorrowExposureAncestorFold.walk]
  have member := covered (index,node) ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present) own
  exact path_of_walk tree depth root index node present _ member

/-- A witness remains either observed or reachable from an actual pending task.
For a postvisit task only the task's own node remains reachable. -/
def Pending (tree : BorrowTree) (witness : UniIndex) (seen : Bool) (stack : Array Task) : Prop :=
  seen = true ∨ ∃ task ∈ stack.toList, Path tree task.1 witness ∧ (task.2 = true → task.1 = witness)

theorem initial {tree root witness} (path : Path tree root witness) : Pending tree witness false #[(root,false)] :=
  .inr ⟨(root,false),by simp,path,by simp⟩

theorem empty {tree witness seen} (pending : Pending tree witness seen #[]) : seen = true := by
  rcases pending with done | ⟨task,member,_,_⟩
  · exact done
  · simp at member

/-- Scalar/cache reasoning must show a skipped subtree cannot contain the
selected supporter; this graph lemma then retains the witness invariant. -/
theorem pop {tree witness seen} (stack : Array Task) (index : UniIndex) (post : Bool)
    (pending : Pending tree witness seen (stack.push (index,post)))
    (excluded : ¬ Path tree index witness) : Pending tree witness seen stack := by
  rcases pending with done | ⟨task,member,path,last⟩
  · exact .inl done
  · simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with earlier | same
    · exact .inr ⟨task,earlier,path,last⟩
    · subst task
      exact False.elim (excluded path)
theorem expand {tree witness} (graph : Reciprocal tree)
    (seen : Bool) (stack : Array Task) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node)
    (pending : Pending tree witness seen (stack.push (index,false))) :
    Pending tree witness seen (expanded stack index node.children) := by
  rcases pending with done | ⟨task,member,path,post⟩
  · exact .inl done
  · simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with member | same
    · refine .inr ⟨task,?_,path,post⟩
      simp [expanded,member]
    · subst task
      by_cases same : index = witness
      · refine .inr ⟨(index,true),?_,path,by intro _;exact same⟩
        simp [expanded]
      · obtain ⟨oldNode,child,found,member,path⟩ := path.first graph same
        have sameNode : oldNode = node := Option.some.inj (found.symm.trans present)
        subst oldNode
        refine .inr ⟨(child,false),?_,path,by simp⟩
        simp only [expanded,Array.toList_append,List.mem_append,Array.toList_map]
        exact .inr (List.mem_map.mpr ⟨child,member,rfl⟩)

theorem post {tree witness} (seen afterSeen : Bool) (stack : Array Task) (index : UniIndex)
    (pending : Pending tree witness seen (stack.push (index,true)))
    (monotone : seen = true → afterSeen = true) (found : index = witness → afterSeen = true) :
    Pending tree witness afterSeen stack := by
  rcases pending with done | ⟨task,member,path,post⟩
  · exact .inl (monotone done)
  · simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
    rcases member with member | same
    · exact .inr ⟨task,member,path,post⟩
    · subst task
      exact .inl (found (post rfl))

end DuplicatePrefix.GeneralBorrowWildcardControlWitness
