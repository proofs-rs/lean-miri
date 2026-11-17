import duplicate_prefix.GeneralBorrowWildcardTaskRegions
namespace DuplicatePrefix.GeneralBorrowWildcardUntouched
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForest GeneralBorrowWildcardSubtreeStack GeneralBorrowWildcardTaskRegions GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Every still-unprocessed task region retains its exact original optional
permission slot. Pending postvisit regions contain only their own node. -/
def Untouched (tree : TraversalTree) (initial current : LocationTree) (stack : Array Task) : Prop :=
  ∀ task ∈ stack.toList, ∀ query, Region tree task query.toNat → current.perms.get query = initial.perms.get query

theorem initial (tree : TraversalTree) (location : LocationTree) (root : UniIndex) :
    Untouched tree location location #[(root,false)] := by intro _ _ _ _;rfl

theorem pop (tree : TraversalTree) (initial current : LocationTree) (stack : Array Task) (task : Task)
    (untouched : Untouched tree initial current (stack.push task)) : Untouched tree initial current stack := by
  intro next member query region
  exact untouched next (by simp [member]) query region

/-- Region inclusion transports exact untouched slots across the actual
parent-postvisit/child-previsit expansion. -/
theorem expand (tree : TraversalTree) (forest : Forest tree) (initial current : LocationTree)
    (stack : Array Task) (index : UniIndex) (children : Array UniIndex) (valid : index.toNat < tree.nodes.size)
    (shape : tree.nodes[index.toNat].children = children.toList.map UniIndex.toNat)
    (untouched : Untouched tree initial current (stack.push (index,false))) :
    Untouched tree initial current (expanded stack index children) := by
  intro task member query region
  simp only [expanded,Array.toList_append,Array.toList_push,Array.toList_map,List.mem_append] at member
  rcases member with old | child
  · rcases old with earlier | parent
    · exact untouched task (by simp [earlier]) query region
    · have same : task = (index,true) := by simpa using parent
      subst task
      exact untouched (index,false) (by simp) query
        (expanded_subset tree forest index children valid shape (index,true) (by simp) query.toNat region)
  · exact untouched (index,false) (by simp) query
      (expanded_subset tree forest index children valid shape task (by simpa using Or.inr child) query.toNat region)

/-- A completed node belongs to none of the remaining task regions. Therefore
an actual callback's other-slot frame preserves the exact untouched frontier. -/
theorem post (tree : TraversalTree) (initial current after : LocationTree)
    (stack : Array Task) (index : UniIndex)
    (disjoint : Disjoint tree (stack.push (index,true)))
    (untouched : Untouched tree initial current (stack.push (index,true)))
    (frame : ∀ query, query ≠ index → after.perms.get query = current.perms.get query) :
    Untouched tree initial after stack := by
  have apart : ∀ task ∈ stack.toList, Apart tree task (index,true) := by
    have all := (List.pairwise_append.mp (by simpa only [Disjoint,Array.toList_push] using disjoint)).2.2
    exact fun task member => all task member (index,true) (by simp)
  intro task member query region
  have different : query ≠ index := by
    intro same
    subst query
    exact apart task member index.toNat ⟨region,rfl⟩
  rw [frame query different]
  exact untouched task (by simp [member]) query region

/-- At the next literal source pop, both previsit and postvisit tasks expose
their exact initial optional permission slot. -/
theorem top (tree : TraversalTree) (initial current : LocationTree) (stack : Array Task)
    (index : UniIndex) (post : Bool) (valid : index.toNat < tree.nodes.size)
    (untouched : Untouched tree initial current (stack.push (index,post))) :
    current.perms.get index = initial.perms.get index := by
  apply untouched (index,post) (by simp) index
  cases post
  · exact Desc.refl index.toNat valid
  · rfl

/-- Source projection supplies the raw child-list shape needed by both
frontier invariants; no operation completion is assumed. -/
theorem expand_actual (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (initial current : LocationTree) (stack : Array Task) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node)
    (disjoint : Disjoint (source_normal_projection tree location protections).topology (stack.push (index,false)))
    (untouched : Untouched (source_normal_projection tree location protections).topology initial current (stack.push (index,false))) :
    Disjoint (source_normal_projection tree location protections).topology (expanded stack index node.children) ∧
    Untouched (source_normal_projection tree location protections).topology initial current (expanded stack index node.children) := by
  have valid : index.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
    have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using bounded
  have projected := projection_topology_node tree location protections index.toNat index node rfl present
  simp only [Array.getElem?_eq_getElem valid,Option.getD_some] at projected
  have shape : ((source_normal_projection tree location protections).topology.nodes[index.toNat]'valid).children = node.children.toList.map UniIndex.toNat := by
    rw [projected]
  exact ⟨GeneralBorrowWildcardTaskRegions.expand _ forest stack index node.children valid shape disjoint,
    expand _ forest initial current stack index node.children valid shape untouched⟩

end DuplicatePrefix.GeneralBorrowWildcardUntouched
