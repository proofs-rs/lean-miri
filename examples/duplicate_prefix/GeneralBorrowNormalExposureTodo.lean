import duplicate_prefix.GeneralBorrowExposurePermissionUpdate
namespace DuplicatePrefix.GeneralBorrowNormalExposureTodo
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowExposureLevelUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Virtual effective levels during the actual post-materialization cache loop:
unprocessed visitors retain old levels, while other nodes use final levels. -/
def levels (todo : List TraversalEvent) (before after : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) : WildcardAccessLevel :=
  if index.toNat ∈ todo.map TraversalEvent.node then effective before protections index node else effective after protections index node

theorem converted_nat (position : Nat) (index : UniIndex) (converted : UniIndex.ofNat? position = some index) : index.toNat = position := by
  unfold UniIndex.ofNat? at converted
  split at converted
  next bounded => cases converted;simp only [UniIndex.toNat,UInt32.toNat_ofNat'];omega
  next => contradiction

theorem coherent_congr (cache : ExposedCache) (nodes : UniValMap TreeNode)
    (before after : UniIndex → TreeNode → WildcardAccessLevel) (coherent : Coherent cache nodes before)
    (same : ∀ index node,nodes.get index = some node → before index node = after index node) : Coherent cache nodes after := by
  intro query kind
  rw [coherent query kind]
  exact congrArg UInt16.ofNat (GeneralBorrowExposurePermissionUpdate.cardinality_congr nodes before after same query kind)

/-- Unvisited effective permissions frame the initial mixed-level invariant. -/
theorem initial (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags) (todo : List TraversalEvent)
    (coherent : LocationCoherent tree before protections)
    (unvisited : ∀ index node,tree.nodeAt index = some node → index.toNat ∉ todo.map TraversalEvent.node →
      effective after protections index node = effective before protections index node) :
    Coherent before.exposedCache tree.nodes (levels todo before after protections) := by
  apply coherent_congr _ _ _ _ coherent
  intro index node present
  by_cases member : index.toNat ∈ todo.map TraversalEvent.node
  · simp only [levels,ite_eq_left member]
  · simp only [levels,ite_eq_right member]
    exact (unvisited index node present member).symm

theorem head_old (_tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (event : TraversalEvent) (rest : List TraversalEvent) (index : UniIndex) (node : TreeNode)
    (converted : UniIndex.ofNat? event.node = some index) :
    levels (event::rest) before after protections index node = effective before protections index node := by
  have same := converted_nat event.node index converted
  simp only [levels,List.map_cons,same,List.mem_cons_self,ite_true]

/-- Distinct real visitors allow one source-level replacement to advance the
virtual invariant exactly to the remaining event list. -/
theorem advance (tree : BorrowTree) (before after : LocationTree) (protections : ProtectedTags)
    (event : TraversalEvent) (rest : List TraversalEvent) (unique : ((event::rest).map TraversalEvent.node).Nodup)
    (index : UniIndex) (node : TreeNode) (converted : UniIndex.ofNat? event.node = some index)
    (present : tree.nodeAt index = some node) (level : WildcardAccessLevel)
    (newLevel : level = effective after protections index node)
    (query : UniIndex) (value : TreeNode) (found : tree.nodeAt query = some value) :
    replace (levels (event::rest) before after protections) index level query value = levels rest before after protections query value := by
  have sameNat := converted_nat event.node index converted
  by_cases same : query = index
  · subst query
    have equal : value = node := Option.some.inj (found.symm.trans present)
    subst value
    have absent : index.toNat ∉ rest.map TraversalEvent.node := by
      rw [sameNat]
      exact (List.nodup_cons.mp unique).1
    simp only [replace,ite_true,levels,ite_eq_right absent,newLevel]
  · have different : query.toNat ≠ event.node := by
      intro equal
      exact same (GeneralBorrowNodeUpdate.index_injective query index (equal.trans sameNat.symm))
    simp only [replace,ite_eq_right same,levels,List.map_cons,List.mem_cons,different,false_or]
end DuplicatePrefix.GeneralBorrowNormalExposureTodo
