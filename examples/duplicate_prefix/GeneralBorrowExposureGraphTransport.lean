import duplicate_prefix.GeneralBorrowExposureEntries
namespace DuplicatePrefix.GeneralBorrowExposureGraphTransport
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowExposureAncestorFold
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual supporting exposed source indices at one queried cache counter. -/
def sources (nodes : UniValMap TreeNode) (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (query : UniIndex) (kind : AccessKind) : List UniIndex :=
  (nodes.entries.toList.filter (contributes nodes levels query kind)).map Prod.fst

theorem sources_nodup (nodes : UniValMap TreeNode) (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (query : UniIndex) (kind : AccessKind) : (sources nodes levels query kind).Nodup := by
  exact List.pairwise_map.mpr ((GeneralBorrowExposureContributionList.entries_keys nodes).filter _)

theorem member (nodes : UniValMap TreeNode) (levels : UniIndex → TreeNode → WildcardAccessLevel)
    (query : UniIndex) (kind : AccessKind) (index : UniIndex) :
    index ∈ sources nodes levels query kind ↔ ∃ node,nodes.get index = some node ∧
      node.isExposed = true ∧ supports (levels index node) kind = true ∧ query ∈ walk nodes (nodes.size+1) index := by
  constructor
  · intro found
    obtain ⟨⟨source,node⟩,qualified,same⟩ := List.mem_map.mp found
    cases same
    have present := (GeneralBorrowFreshReuseProtection.entries_get nodes source node).mp (List.mem_filter.mp qualified).1
    have conditions := (List.mem_filter.mp qualified).2
    simp only [contributes,Bool.and_eq_true,List.contains_iff_mem] at conditions
    exact ⟨node,present,conditions.1.1,conditions.1.2,conditions.2⟩
  · rintro ⟨node,present,exposed,supported,ancestor⟩
    apply List.mem_map.mpr
    refine ⟨(index,node),List.mem_filter.mpr ⟨(GeneralBorrowFreshReuseProtection.entries_get nodes index node).mpr present,?_⟩,rfl⟩
    simp only [contributes,exposed,supported,Bool.true_and,List.contains_iff_mem]
    exact ancestor

/-- Cardinality depends only on the actual exposed supporting ancestor witnesses,
not on node SIFA, child arrays, row order or vacant slots. -/
theorem cardinality_eq (before after : UniValMap TreeNode)
    (oldLevels newLevels : UniIndex → TreeNode → WildcardAccessLevel)
    (same : ∀ query kind index,
      (∃ node,before.get index = some node ∧ node.isExposed = true ∧ supports (oldLevels index node) kind = true ∧
        query ∈ walk before (before.size+1) index) ↔
      (∃ node,after.get index = some node ∧ node.isExposed = true ∧ supports (newLevels index node) kind = true ∧
        query ∈ walk after (after.size+1) index)) (query : UniIndex) (kind : AccessKind) :
    cardinality after newLevels query kind = cardinality before oldLevels query kind := by
  have equivalent : (sources after newLevels query kind).Perm (sources before oldLevels query kind) :=
    (List.perm_ext_iff_of_nodup (sources_nodup after newLevels query kind)
      (sources_nodup before oldLevels query kind)).mpr (fun index => by
        rw [member,member];exact (same query kind index).symm)
  simpa only [sources,List.length_map,cardinality] using equivalent.length_eq

/-- Old parent paths are unchanged under a metadata-preserving extension,
provided both source walk budgets exceed the original node's depth. -/
theorem walk_extension (before after : UniValMap TreeNode) (depth : GeneralBorrowExposure.ParentDepth before)
    (parents : ∀ index node,before.get index = some node →
      ∃ next,after.get index = some next ∧ next.parent = node.parent)
    (fuel other : Nat) (index : UniIndex) (node : TreeNode) (present : before.get index = some node)
    (room : depth.depth index < fuel) (otherRoom : depth.depth index < other) :
    walk after other index = walk before fuel index := by
  induction fuel generalizing other index node with
  | zero => omega
  | succ fuel ih =>
    cases other with
    | zero => omega
    | succ other =>
      obtain ⟨next,found,parentSame⟩ := parents index node present
      simp only [walk,present,found,parentSame]
      cases parent : node.parent with
      | none => rfl
      | some ancestor =>
        obtain ⟨ancestorNode,ancestorFound,smaller⟩ := depth.parent index node present ancestor parent
        exact congrArg (List.cons index) (ih other ancestor ancestorNode ancestorFound (by omega) (by omega))

/-- A fresh unexposed extension or a SIFA-only rewrite does not change any
support count when old parents, flags and effective levels are preserved.
The reverse record is needed only for exposed nodes, so fresh unexposed nodes
require no permissions or cache witnesses. -/
theorem extension (before after : UniValMap TreeNode) (depth : GeneralBorrowExposure.ParentDepth before)
    (oldLevels newLevels : UniIndex → TreeNode → WildcardAccessLevel)
    (size : before.size ≤ after.size)
    (old : ∀ index node,before.get index = some node → ∃ next,after.get index = some next ∧
      next.parent = node.parent ∧ next.isExposed = node.isExposed ∧ newLevels index next = oldLevels index node)
    (back : ∀ index next,after.get index = some next → next.isExposed = true →
      ∃ node,before.get index = some node)
    (query : UniIndex) (kind : AccessKind) : cardinality after newLevels query kind = cardinality before oldLevels query kind := by
  apply cardinality_eq
  intro query kind index
  constructor
  · rintro ⟨node,present,exposed,support,ancestor⟩
    obtain ⟨next,found,parentSame,exposedSame,levelSame⟩ := old index node present
    refine ⟨next,found,exposedSame.trans exposed,?_,?_⟩
    · rw [levelSame];exact support
    · rw [walk_extension before after depth (fun i n p => by obtain ⟨v,f,h,_⟩ := old i n p;exact ⟨v,f,h⟩)
        (before.size+1) (after.size+1) index node present (by have := depth.bounded index node present;omega)
        (by have := depth.bounded index node present;omega)]
      exact ancestor
  · rintro ⟨next,found,exposed,support,ancestor⟩
    obtain ⟨node,present⟩ := back index next found exposed
    obtain ⟨value,valueFound,parentSame,exposedSame,levelSame⟩ := old index node present
    have equal : value = next := Option.some.inj (valueFound.symm.trans found)
    subst value
    refine ⟨node,present,exposedSame.symm.trans exposed,?_,?_⟩
    · rw [←levelSame];exact support
    · rw [walk_extension before after depth (fun i n p => by obtain ⟨v,f,h,_⟩ := old i n p;exact ⟨v,f,h⟩)
        (before.size+1) (after.size+1) index node present (by have := depth.bounded index node present;omega)
        (by have := depth.bounded index node present;omega)] at ancestor
      exact ancestor

end DuplicatePrefix.GeneralBorrowExposureGraphTransport
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowExposureGraphTransport.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved cache graph transport dependency {dependency}"
