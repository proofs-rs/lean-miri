import duplicate_prefix.GeneralBorrowGcExposedRetained
import duplicate_prefix.GeneralBorrowFreshReuseProtection

namespace DuplicatePrefix.GeneralBorrowGcProvenanceLive
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private abbrev scan (row : UniIndex × TreeNode) (tags : Array BorTag) : Id (ForInStep (Array BorTag)) :=
  if row.2.isExposed = true then .yield (tags.push row.2.tag) else .yield tags

private theorem keep (rows : List (UniIndex × TreeNode)) (tag : BorTag) (seed : Array BorTag)
    (member : tag ∈ seed) : tag ∈ (forIn (m := Id) rows seed scan).run := by
  apply DuplicatePrefix.GeneralBorrowLoop.list_invariant rows scan (fun tags => tag ∈ tags)
  · intro row inside tags present
    cases exposed : row.2.isExposed with
    | false => simpa only [scan,exposed,Bool.false_eq_true,ite_false,ForInStep.value] using present
    | true => simpa only [scan,exposed,ite_true,ForInStep.value] using Array.mem_push.mpr (Or.inl present)
  · exact member

private theorem listed (rows : List (UniIndex × TreeNode)) (row : UniIndex × TreeNode)
    (member : row ∈ rows) (exposed : row.2.isExposed = true) (seed : Array BorTag) :
    row.2.tag ∈ (forIn (m := Id) rows seed scan).run := by
  induction rows generalizing seed with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | tail
    · subst first
      simp only [List.forIn_cons,scan,exposed,ite_true,bind]
      exact keep rest row.2.tag (seed.push row.2.tag) (Array.mem_push.mpr (Or.inr rfl))
    · rw [List.forIn_cons]
      unfold scan
      split <;> simpa only [bind,scan] using ih tail _

/-- The ACTUAL provenance visitor supplies every exposed tag required by the
GC retention/cache theorem. All roots may add further tags; no synthetic
liveness set or assumed traversal outcome replaces the source visitor. -/
theorem provenance (tree : BorrowTree) : GeneralBorrowGcExposedRetained.ExposedLive tree tree.provenanceTags := by
  intro index node present exposed
  have member := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr present
  unfold BorrowTree.provenanceTags
  simp only [Id.run,bind,pure,←Array.forIn_toList]
  apply Array.contains_iff_mem.mpr
  change node.tag ∈ (forIn (m := Id) tree.nodes.entries.toList _ scan).run
  exact listed tree.nodes.entries.toList (index,node) member exposed _

end DuplicatePrefix.GeneralBorrowGcProvenanceLive
