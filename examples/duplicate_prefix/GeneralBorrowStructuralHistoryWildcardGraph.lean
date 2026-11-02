import duplicate_prefix.GeneralBorrowStructuralHistoryState
import duplicate_prefix.GeneralBorrowPositiveWildcardConstructor
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryWildcardGraph
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState GeneralBorrowExposure GeneralBorrowGraph
open GeneralBorrowGcDfsGraphRestoration
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
noncomputable section

def rank (tree : BorrowTree) (initial : GraphState tree) : UniIndex → Nat :=
  fun index => (Classical.choice (initial.forest ⟨{},{}⟩ {})).rank index.toNat

theorem graph (tree : BorrowTree) (initial : GraphState tree) : Graph (rank tree initial) tree := by
  let forest := Classical.choice (initial.forest ⟨{},{}⟩ {})
  let depth := Classical.choice initial.depth
  let metadata := GeneralBorrowGcDfsReadyFormation.metadata tree ⟨{},{}⟩ {} forest initial.children
  have backlinks := GeneralBorrowGcDfsBacklinks.of_forest tree ⟨{},{}⟩ {} forest depth
  refine ⟨?_,metadata.children,metadata.distinct⟩
  intro child node present parent edge
  obtain ⟨parentNode,parentPresent,member⟩ := backlinks child node present parent edge
  exact ⟨parentNode,parentPresent,member,(GeneralBorrowGcDfsParentPaths.original_edge tree ⟨{},{}⟩ {} forest child node present parent edge).2⟩

/-- A vacant sparse slot becomes a genuine isolated root. This source graph
transport handles both append and reuse; no final Forest is supplied. -/
theorem extension (tree : BorrowTree) (initial : GraphState tree) (mapping : UniKeyMap BorTag)
    (index : UniIndex) (tag : BorTag) (outside : Permission) (sifa : IdempotentForeignAccess)
    (vacant : tree.nodes.get index = none) :
    Graph (fun query => if query=index then 0 else rank tree initial query)
      (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa) := by
  let old := graph tree initial
  let newNode := WildcardHitZeroConstructor.rootNode tag outside sifa
  have different : ∀ query node, tree.nodes.get query=some node → query≠index := by
    intro query node found same
    subst query
    rw [vacant] at found
    cases found
  constructor
  · intro child node present parent edge
    change (tree.nodes.insert index newNode).get child=some node at present
    by_cases same : child=index
    · subst child
      rw [GeneralBorrowFreshLocation.get_same] at present
      cases present
      cases edge
    · rw [GeneralBorrowFreshLocation.get_other _ index child newNode same] at present
      obtain ⟨parentNode,parentPresent,member,strict⟩ := old.parents child node present parent edge
      have parentDifferent := different parent parentNode parentPresent
      refine ⟨parentNode,?_,member,?_⟩
      · exact (GeneralBorrowFreshLocation.get_other _ index parent newNode parentDifferent).trans parentPresent
      · simpa only [same,parentDifferent,ite_false] using strict
  · intro parent node present child member
    change (tree.nodes.insert index newNode).get parent=some node at present
    by_cases same : parent=index
    · subst parent
      rw [GeneralBorrowFreshLocation.get_same] at present
      cases present
      simp [newNode,WildcardHitZeroConstructor.rootNode] at member
    · rw [GeneralBorrowFreshLocation.get_other _ index parent newNode same] at present
      obtain ⟨childNode,childPresent,edge⟩ := old.children parent node present child member
      exact ⟨childNode,(GeneralBorrowFreshLocation.get_other _ index child newNode (different child childNode childPresent)).trans childPresent,edge⟩
  · intro parent node present
    change (tree.nodes.insert index newNode).get parent=some node at present
    by_cases same : parent=index
    · subst parent
      rw [GeneralBorrowFreshLocation.get_same] at present
      cases present
      simp [newNode,WildcardHitZeroConstructor.rootNode]
    · rw [GeneralBorrowFreshLocation.get_other _ index parent newNode same] at present
      exact old.distinct parent node present

theorem covered (tree : BorrowTree) (initial : GraphState tree) (mapping : UniKeyMap BorTag)
    (index : UniIndex) (tag : BorTag) (outside : Permission) (sifa : IdempotentForeignAccess) :
    RootsCover (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa) := by
  intro query node present parentless
  change (tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag outside sifa)).get query=some node at present
  change query ∈ (tree.roots.push index).toList
  by_cases same : query=index
  · subst query;simp
  · rw [GeneralBorrowFreshLocation.get_other _ index query _ same] at present
    have member := initial.covered query node present parentless
    simp [member]

theorem root_nodes (tree : BorrowTree) (initial : GraphState tree) (mapping : UniKeyMap BorTag)
    (index : UniIndex) (tag : BorTag) (outside : Permission) (sifa : IdempotentForeignAccess)
    (vacant : tree.nodes.get index=none) :
    ∀ root ∈ (WildcardHitZeroConstructor.installed tree mapping index tag outside sifa).roots.toList,
      ∃ node,(WildcardHitZeroConstructor.installed tree mapping index tag outside sifa).nodes.get root=some node ∧ node.parent=none := by
  intro root member
  change root ∈ (tree.roots.push index).toList at member
  rw [Array.toList_push,List.mem_append,List.mem_singleton] at member
  rcases member with old | same
  · obtain ⟨node,present,parentless⟩ := initial.rootNodes root old
    have different : root≠index := by intro same;subst root;rw[vacant] at present;cases present
    exact ⟨node,(GeneralBorrowFreshLocation.get_other _ index root _ different).trans present,parentless⟩
  · subst root
    exact ⟨_,GeneralBorrowFreshLocation.get_same _ index _,rfl⟩
end
end DuplicatePrefix.GeneralBorrowStructuralHistoryWildcardGraph
