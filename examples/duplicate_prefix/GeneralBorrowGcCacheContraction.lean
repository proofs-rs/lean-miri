import duplicate_prefix.GeneralBorrowExposureGraphTransport
import duplicate_prefix.GeneralBorrowExposureAncestorDistinct

namespace DuplicatePrefix.GeneralBorrowGcCacheContraction
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureAncestorFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Pure parent-map contraction. The deleted node's immediate children point
at its old parent; all other edges retain their exact values. This describes
an ATOMIC GC collapse, not its temporarily dangling intermediate deletion. -/
structure Contract (before after : UniValMap TreeNode) (removed : UniIndex) (node : TreeNode) where
  present : before.get removed = some node
  absent : after.get removed = none
  size : before.size ≤ after.size
  forward : ∀ index old, before.get index = some old → index ≠ removed →
    ∃ next, after.get index = some next ∧
      next.parent = if old.parent = some removed then node.parent else old.parent
  backward : ∀ index next, after.get index = some next →
    index ≠ removed ∧ ∃ old, before.get index = some old

/-- A contraction retains the OLD bounded rank; no final graph certificate is
assumed. In particular every surviving node's actual parent is present. -/
def Contract.depth {before after : UniValMap TreeNode} {removed : UniIndex} {node : TreeNode}
    (data : Contract before after removed node) (oldDepth : ParentDepth before) : ParentDepth after := by
  refine ⟨oldDepth.depth,?_,?_⟩
  · intro index next found
    obtain ⟨_,old,present⟩ := data.backward index next found
    exact Nat.le_trans (oldDepth.bounded index old present) data.size
  · intro index next found parent parentEq
    obtain ⟨different,old,present⟩ := data.backward index next found
    obtain ⟨actual,lookup,edge⟩ := data.forward index old present different
    have same : actual = next := Option.some.inj (lookup.symm.trans found)
    subst actual
    by_cases skipped : old.parent = some removed
    · rw [ite_eq_left skipped] at edge
      obtain ⟨_,_,smaller⟩ := oldDepth.parent index old present removed skipped
      obtain ⟨ancestor,ancestorFound,ancestorSmaller⟩ := oldDepth.parent removed node data.present parent (edge.symm.trans parentEq)
      have notRemoved : parent ≠ removed := by intro eq;subst parent;omega
      obtain ⟨value,valueFound,_⟩ := data.forward parent ancestor ancestorFound notRemoved
      exact ⟨value,valueFound,by omega⟩
    · rw [ite_eq_right skipped] at edge
      have original : old.parent = some parent := edge.symm.trans parentEq
      have notRemoved : parent ≠ removed := by intro eq;subst parent;exact skipped original
      obtain ⟨ancestor,ancestorFound,smaller⟩ := oldDepth.parent index old present parent original
      obtain ⟨value,valueFound,_⟩ := data.forward parent ancestor ancestorFound notRemoved
      exact ⟨value,valueFound,smaller⟩

/-- At every surviving query, the actual bounded ancestor walk has exactly its
old members. A skipped intermediate consumes one fewer traversal step. -/
theorem walk_member {before after : UniValMap TreeNode} {removed : UniIndex} {node : TreeNode}
    (data : Contract before after removed node) (depth : ParentDepth before)
    (fuel other : Nat) (index : UniIndex) (old : TreeNode) (present : before.get index = some old)
    (different : index ≠ removed) (room : depth.depth index < fuel) (otherRoom : depth.depth index < other)
    (query : UniIndex) (queryDifferent : query ≠ removed) :
    query ∈ walk after other index ↔ query ∈ walk before fuel index := by
  induction fuel generalizing other index old with
  | zero => omega
  | succ fuel ih =>
    cases other with
    | zero => omega
    | succ other =>
      obtain ⟨next,found,edge⟩ := data.forward index old present different
      simp only [walk,found,present]
      cases parentEq : old.parent with
      | none => simp only [parentEq,reduceCtorEq,ite_false] at edge;rw [edge]
      | some parent =>
        obtain ⟨parentNode,parentFound,parentSmaller⟩ := depth.parent index old present parent parentEq
        by_cases skipped : parent = removed
        · subst parent
          have same : parentNode = node := Option.some.inj (parentFound.symm.trans data.present)
          subst parentNode
          simp only [parentEq,ite_true] at edge
          rw [edge]
          cases fuel with
          | zero => omega
          | succ fuel =>
            simp only [walk,data.present]
            cases grandEq : node.parent with
            | none => simp only [List.mem_cons,List.not_mem_nil,or_false];simp_all
            | some grand =>
              obtain ⟨ancestor,ancestorFound,ancestorSmaller⟩ := depth.parent removed node data.present grand grandEq
              have grandDifferent : grand ≠ removed := by intro same;subst grand;omega
              have recur := ih (other := other) (index := grand) (old := ancestor) ancestorFound grandDifferent
                (by omega) (by omega)
              have budgets := GeneralBorrowExposureGraphTransport.walk_extension before before depth
                (fun i n p => ⟨n,p,rfl⟩) (fuel+1) fuel grand ancestor ancestorFound (by omega) (by omega)
              rw [←budgets] at recur
              simp only [List.mem_cons]
              exact or_congr Iff.rfl (by simpa only [List.mem_cons,queryDifferent,false_or] using recur)
        · simp only [parentEq,Option.some.injEq,ite_eq_right skipped] at edge
          rw [edge]
          simp only [List.mem_cons]
          exact or_congr Iff.rfl (ih other parent parentNode parentFound skipped (by omega) (by omega))

end DuplicatePrefix.GeneralBorrowGcCacheContraction
