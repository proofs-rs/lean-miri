import duplicate_prefix.GenericTagHighWaterPreservation
import duplicate_prefix.GeneralBorrowGcWhileInvariant
import duplicate_prefix.GeneralBorrowGcRootInvariant

namespace DuplicatePrefix.GenericTagHighWaterGc
open Miri Miri.ABI Miri.Interpreter Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GenericFunctionTagFormation GenericTagHighWaterPreservation GeneralBorrowFreshLocation GeneralBorrowGcWalker
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
private theorem nodes_of_entries (tree : BorrowTree) (counter : BorTag)
    (below : ∀ row ∈ tree.nodes.entries, row.2.tag.value.toNat < counter.value.toNat) : NodesBelow tree.nodes counter := by
  intro query node present
  exact below (query,node) (Array.mem_def.mpr ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes query node).mpr present))

set_option autoImplicit false in
private theorem entries_of_nodes (tree : BorrowTree) (counter : BorTag) (below : NodesBelow tree.nodes counter) :
    ∀ row ∈ tree.nodes.entries, row.2.tag.value.toNat < counter.value.toNat := by
  intro row member
  exact below row.1 row.2 ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp (Array.mem_def.mp member))

set_option autoImplicit false in
private theorem map_removed (mapping : UniKeyMap BorTag) (tag counter : BorTag)
    (below : ∀ row ∈ mapping.mapping, row.1.value.toNat < counter.value.toNat) :
    ∀ row ∈ (mapping.remove tag).mapping, row.1.value.toNat < counter.value.toNat := by
  unfold UniKeyMap.remove
  split
  · exact below
  · intro row member
    exact below row (Array.mem_filter.mp member).1

set_option autoImplicit false in
/-- GC's actual existing-node rewrite changes links and source metadata while
retaining the stored tag. No new tag-bound premise is needed. -/
theorem insert_existing (tree : BorrowTree) (index : UniIndex) (oldNode newNode : TreeNode)
    (present : tree.nodes.get index = some oldNode) (sameTag : newNode.tag = oldNode.tag)
    (protections : ProtectedTags) (counter : BorTag) (below : Below tree protections counter) :
    Below {tree with nodes := tree.nodes.insert index newNode} protections counter := by
  have previous := nodes_of_entries tree counter below.nodes
  have newBound : newNode.tag.value.toNat < counter.value.toNat := by rw [sameTag];exact previous index oldNode present
  refine ⟨below.mapping,?_,below.protectors⟩
  apply entries_of_nodes
  intro query node lookup
  change (tree.nodes.insert index newNode).get query = some node at lookup
  by_cases same : query=index
  · subst query
    rw [get_same] at lookup
    cases lookup
    exact newBound
  · rw [get_other tree.nodes index query newNode same] at lookup
    exact previous query node lookup

set_option autoImplicit false in
/-- The exact production remove_useless_node primitive preserves high-water
bounds on both its removal branch and MissingNode branch. This is a data
invariant for returned states, not a successful-GC or safe-error claim. -/
theorem remove_primitive (tree : BorrowTree) (index : UniIndex) (protections : ProtectedTags) (counter : BorTag)
    (below : Below tree protections counter) : Below (source_remove_useless_node tree index).1 protections counter := by
  cases stored : tree.nodes.get index with
  | none =>
    unfold_source_remove_useless_node
    simpa only [stored,Id.run,bind,pure] using below
  | some node =>
    unfold_source_remove_useless_node
    simp only [stored,Id.run,bind,pure]
    refine ⟨map_removed tree.tagMapping node.tag counter below.mapping,?_,below.protectors⟩
    apply entries_of_nodes
    intro query old present
    change (tree.nodes.remove index).get query = some old at present
    by_cases same : query=index
    · subst query
      rw [GeneralBorrowFreshDeassignment.get_removed] at present
      cases present
    · rw [GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query same] at present
      exact nodes_of_entries tree counter below.nodes query old present

set_option autoImplicit false in
/-- The actual GC postorder while loop preserves every stored-tag bound,
including states returned with an error outcome. -/
theorem children_preserves (tree : BorrowTree) (root : UniIndex) (liveTags : Array BorTag)
    (protections : ProtectedTags) (counter : BorTag) (below : Below tree protections counter) :
    Below (source_gc_children tree root liveTags).tree protections counter := by
  exact GeneralBorrowGcWhileInvariant.preserves (fun current => Below current protections counter)
    (fun current index good => remove_primitive current index protections counter good)
    (fun current index oldNode newNode present same good => insert_existing current index oldNode newNode present same protections counter good)
    tree root liveTags below

set_option autoImplicit false in
/-- Full production removeUnreachableTags preserves the same map, node and
per-global protector bounds. No successful outcome, GC eligibility, graph
validity, live-tag coverage or valid-history premise is assumed. -/
theorem remove_unreachable (tree : BorrowTree) (liveTags : Array BorTag)
    (protections : ProtectedTags) (counter : BorTag) (below : Below tree protections counter) :
    Below (tree.removeUnreachableTags liveTags).tree protections counter := by
  apply GeneralBorrowGcRootInvariant.preserves (fun current => Below current protections counter) tree liveTags below
  · intro current root good
    change Below (source_gc_children current root liveTags).tree protections counter
    exact children_preserves current root liveTags protections counter good
  · intro current good
    exact ⟨good.mapping,good.nodes,good.protectors⟩

end DuplicatePrefix.GenericTagHighWaterGc

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GenericTagHighWaterGc.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved GC high-water dependency {name}: {dependency}"
