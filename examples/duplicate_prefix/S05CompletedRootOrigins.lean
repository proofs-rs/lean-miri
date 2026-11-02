import duplicate_prefix.CandidateStableCallOwnership
import duplicate_prefix.GeneralBorrowStructuralHistoryState
import duplicate_prefix.GeneralBorrowGcDfsOriginalEdges
import duplicate_prefix.GeneralBorrowExposedScopedReciprocal
import duplicate_prefix.GeneralBorrowWildcardParentTagOrder

/-! A bounded graph characterization of joint completion existence. This does
not embed resource families or establish admission of ordinary callers. -/
namespace DuplicatePrefix.S05CompletedRootOrigins
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowStructuralHistoryState
open GeneralBorrowExposedNonleafPrimaryPath GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Every later physical root has an exposed older origin in an earlier root. -/
def RootOrigins (tree : BorrowTree) : Prop :=
  ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → position ≠ 0 →
    ∃ (earlier : Nat) (originRoot origin : UniIndex) (rootNode originNode : TreeNode),
      earlier < position ∧ tree.roots[earlier]? = some originRoot ∧
      tree.nodes.get root = some rootNode ∧ tree.nodes.get origin = some originNode ∧
      originNode.isExposed = true ∧ originNode.tag.value < rootNode.tag.value ∧
      Path tree originRoot origin

private theorem position_unique (tree : BorrowTree) (nodup : tree.roots.toList.Nodup)
    (i j : Nat) (root : UniIndex) (first : tree.roots[i]? = some root)
    (second : tree.roots[j]? = some root) : i = j := by
  have valid := (Array.getElem?_eq_some_iff.mp first).choose
  apply (List.Nodup.getElem?_inj (by simpa using valid) nodup).mp
  simpa only [Array.getElem?_toList] using first.trans second.symm

private theorem parent_strict (tree : BorrowTree) (graph : GraphState tree)
    (order : ParentTagOrder tree) (child parent : UniIndex) (node : TreeNode)
    (present : tree.nodes.get child = some node) (edge : node.parent = some parent) :
    ∃ parentNode, tree.nodes.get parent = some parentNode ∧ parentNode.tag.value < node.tag.value := by
  obtain ⟨depth⟩ := graph.depth
  obtain ⟨parentNode,found,less⟩ := depth.parent child node present parent edge
  refine ⟨parentNode,found,?_⟩
  have le := order child node present parent parentNode edge found
  have ne : parentNode.tag.value ≠ node.tag.value := by
    intro same
    have tags : parentNode.tag = node.tag := by
      cases left : parentNode.tag with
      | mk leftValue leftNonzero =>
        cases right : node.tag with
        | mk rightValue rightNonzero =>
          simp only [left, right] at same
          cases same
          rfl
    have mapping := graph.allocator.nodeTags parent parentNode found
    rw [tags, graph.allocator.nodeTags child node present] at mapping
    have equal := Option.some.inj mapping
    rw [equal] at less
    exact Nat.lt_irrefl _ less
  exact UInt64.lt_iff_toNat_lt.mpr (by
    have leNat := UInt64.le_iff_toNat_le.mp le
    have neNat : parentNode.tag.value.toNat ≠ node.tag.value.toNat := by
      intro equal; exact ne (UInt64.toNat_inj.mp equal)
    omega)

private def OriginAt (tree : BorrowTree) (root origin : UniIndex) : Prop :=
  ∃ position earlier originRoot rootNode originNode,
    tree.roots[position]? = some root ∧ position ≠ 0 ∧ earlier < position ∧
    tree.roots[earlier]? = some originRoot ∧ tree.nodes.get root = some rootNode ∧
    tree.nodes.get origin = some originNode ∧ originNode.isExposed = true ∧
    originNode.tag.value < rootNode.tag.value ∧ Path tree originRoot origin

private noncomputable def attachment (tree : BorrowTree) (root : UniIndex) : Option UniIndex :=
  by
    classical
    exact if h : ∃ origin, OriginAt tree root origin then some h.choose else none

private theorem attachment_some (tree : BorrowTree) (root origin : UniIndex)
    (hit : attachment tree root = some origin) : OriginAt tree root origin := by
  unfold attachment at hit
  split at hit
  · have same := Option.some.inj hit
    exact same ▸ Classical.choose_spec ‹∃ origin, OriginAt tree root origin›
  · contradiction

private noncomputable def parentAt (tree : BorrowTree) (index : UniIndex) : Option UniIndex :=
  match tree.nodes.get index with
  | none => none
  | some node => match node.parent with
    | some parent => some parent
    | none => attachment tree index

private noncomputable def completion (tree : BorrowTree) : Completion where
  parents := Array.ofFn fun i : Fin tree.nodes.data.size => parentAt tree ⟨UInt32.ofNat i.val⟩
  depths := Array.ofFn fun i : Fin tree.nodes.data.size =>
    ((tree.nodes.get ⟨UInt32.ofNat i.val⟩).map (fun node => node.tag.value.toNat)).getD 0

private theorem parent_lookup (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    (completion tree).parents[index.toNat]? = some (parentAt tree index) := by
  have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
  simp only [completion, Array.getElem?_ofFn, valid, ↓reduceDIte]
  simp only [UniIndex.toNat, UInt32.ofNat_toNat]

private theorem depth_lookup (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    (completion tree).depths[index.toNat]?.getD 0 = node.tag.value.toNat := by
  have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes index node present
  simp only [completion, Array.getElem?_ofFn, valid, ↓reduceDIte]
  simp only [UniIndex.toNat, UInt32.ofNat_toNat, present, Option.map_some, Option.getD_some]


private theorem chosen_root (tree : BorrowTree) (nodup : tree.roots.toList.Nodup)
    (origins : RootOrigins tree) (position : Nat) (root : UniIndex)
    (lookup : tree.roots[position]? = some root) :
    if position = 0 then attachment tree root = none
    else ∃ earlier originRoot origin rootNode originNode,
      earlier < position ∧ tree.roots[earlier]? = some originRoot ∧
      tree.nodes.get root = some rootNode ∧ tree.nodes.get origin = some originNode ∧
      originNode.isExposed = true ∧ originNode.tag.value < rootNode.tag.value ∧
      Path tree originRoot origin ∧ attachment tree root = some origin := by
  classical
  split
  · rename_i zero
    unfold attachment
    split
    · rename_i existsOrigin
      obtain ⟨origin, pos, earlier, originRoot, rootNode, originNode, found, positive, rest⟩ := existsOrigin
      exact False.elim (positive ((position_unique tree nodup pos position root found lookup).trans zero))
    · rfl
  · rename_i positive
    obtain ⟨earlier, originRoot, origin, rootNode, originNode, lower, previous, liveRoot,
      liveOrigin, exposed, older, path⟩ := origins position root lookup positive
    have available : ∃ origin, OriginAt tree root origin :=
      ⟨origin, position, earlier, originRoot, rootNode, originNode, lookup, positive,
        lower, previous, liveRoot, liveOrigin, exposed, older, path⟩
    have selected : OriginAt tree root available.choose := available.choose_spec
    obtain ⟨pos, earlier, originRoot, rootNode, originNode, found, _, lower, previous,
      liveRoot, liveOrigin, exposed, older, path⟩ := selected
    have equal := position_unique tree nodup pos position root found lookup
    subst pos
    exact ⟨earlier, originRoot, available.choose, rootNode, originNode, lower, previous,
      liveRoot, liveOrigin, exposed, older, path, by simp only [attachment, dite_eq_left available]⟩

private theorem completion_edges (tree : BorrowTree) (graph : GraphState tree)
    (order : ParentTagOrder tree) (child parent : UniIndex)
    (edge : (completion tree).parents[child.toNat]? = some (some parent)) :
    (∃ childNode, tree.nodes.get child = some childNode) ∧
    (∃ parentNode, tree.nodes.get parent = some parentNode) ∧
    (completion tree).depths[parent.toNat]?.getD 0 < (completion tree).depths[child.toNat]?.getD 0 := by
  have valid : child.toNat < tree.nodes.data.size := by
    by_cases bounded : child.toNat < tree.nodes.data.size
    · exact bounded
    · simp only [completion, Array.getElem?_ofFn, dite_eq_right bounded] at edge
      contradiction
  have raw : parentAt tree child = some parent := by
    simp only [completion, Array.getElem?_ofFn, dite_eq_left valid] at edge
    simpa only [UniIndex.toNat, UInt32.ofNat_toNat, Option.some.injEq] using edge
  cases present : tree.nodes.get child with
  | none => simp only [parentAt, present] at raw; contradiction
  | some node =>
    have older : ∃ parentNode, tree.nodes.get parent = some parentNode ∧ parentNode.tag.value < node.tag.value := by
      cases physical : node.parent with
      | some actual =>
        have same : actual = parent := by simpa only [parentAt, present, physical, Option.some.injEq] using raw
        subst actual
        exact parent_strict tree graph order child parent node present physical
      | none =>
        have selected : attachment tree child = some parent := by simpa only [parentAt, present, physical] using raw
        obtain ⟨_, _, _, rootNode, parentNode, _, _, _, _, childFound, parentFound, _, lower, _⟩ :=
          attachment_some tree child parent selected
        have same := Option.some.inj (childFound.symm.trans present)
        subst rootNode
        exact ⟨parentNode, parentFound, lower⟩
    obtain ⟨parentNode, parentFound, lower⟩ := older
    exact ⟨⟨node,rfl⟩, ⟨parentNode,parentFound⟩, by
      rw [depth_lookup tree parent parentNode parentFound, depth_lookup tree child node present]
      exact UInt64.lt_iff_toNat_lt.mp lower⟩

/-- The per-root origin condition constructs ONE joint finite completion. Its
choices are fixed for the graph and reused across all byte rows and queries.
This theorem does not establish resource-family compatibility or coverage of
ordinary inputs. -/
theorem exists_completion (tree : BorrowTree) (graph : GraphState tree)
    (nodup : tree.roots.toList.Nodup) (order : ParentTagOrder tree)
    (origins : RootOrigins tree) : ∃ completed, Completes tree completed := by
  obtain ⟨depth⟩ := graph.depth
  let location : LocationTree := ⟨{},{}⟩
  obtain ⟨forest⟩ := graph.forest location {}
  have reciprocal := GeneralBorrowExposedScopedReciprocal.of_forest tree location {} forest depth
  refine ⟨completion tree, ?_, ?_, nodup, ?_, ?_, ?_, completion_edges tree graph order⟩
  · simp only [completion, Array.size_ofFn]
  · simp only [completion, Array.size_ofFn]
  · intro position root lookup
    exact graph.rootNodes root (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
  · intro index node present
    refine ⟨graph.allocator.nodeTags index node present, ?_, ?_, ?_⟩
    · intro child
      constructor
      · exact GeneralBorrowGcDfsOriginalEdges.children tree location {} forest graph.children index node present child
      · rintro ⟨childNode, childPresent, edge⟩
        obtain ⟨parentNode, parentPresent, member⟩ := reciprocal child childNode childPresent index edge
        have same := Option.some.inj (parentPresent.symm.trans present)
        exact same ▸ member
    · intro parent edge
      rw [parent_lookup tree index node present]
      simp only [parentAt, present, edge]
    · constructor
      · exact graph.covered index node present
      · intro member
        obtain ⟨rootNode, rootFound, parentless⟩ := graph.rootNodes index member
        have same := Option.some.inj (rootFound.symm.trans present)
        exact same ▸ parentless
  · intro position root lookup
    obtain ⟨node, present, parentless⟩ := graph.rootNodes root
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup))
    have selected := chosen_root tree nodup origins position root lookup
    rw [parent_lookup tree root node present]
    rw [show parentAt tree root = attachment tree root by simp only [parentAt, present, parentless]]
    by_cases zero : position = 0
    · simp only [zero, ↓reduceIte] at selected ⊢
      exact congrArg some selected
    · simp only [zero, ↓reduceIte] at selected ⊢
      obtain ⟨earlier, originRoot, origin, rootNode, originNode, lower, previous,
        liveRoot, liveOrigin, exposed, older, path, chosen⟩ := selected
      exact ⟨earlier, originRoot, origin, rootNode, originNode, lower, previous,
        liveRoot, liveOrigin, exposed, older, path, congrArg some chosen⟩

/-- Exact graph-level characterization; it does not assert that structural
ordering alone supplies exposed origins. -/
theorem exists_completion_iff (tree : BorrowTree) (graph : GraphState tree)
    (nodup : tree.roots.toList.Nodup) (order : ParentTagOrder tree) :
    (∃ completed, Completes tree completed) ↔ RootOrigins tree := by
  constructor
  · rintro ⟨completed, complete⟩ position root lookup positive
    have chosen := complete.2.2.2.2.2.1 position root lookup
    simp only [positive, ↓reduceIte] at chosen
    obtain ⟨earlier, originRoot, origin, rootNode, originNode, lower, previous,
      liveRoot, liveOrigin, exposed, older, path, _⟩ := chosen
    exact ⟨earlier, originRoot, origin, rootNode, originNode, lower, previous,
      liveRoot, liveOrigin, exposed, older, path⟩
  · exact exists_completion tree graph nodup order

end DuplicatePrefix.S05CompletedRootOrigins

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.S05CompletedRootOrigins.exists_completion,
      ``DuplicatePrefix.S05CompletedRootOrigins.exists_completion_iff] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "completed root origins depends on unapproved axiom {dependency}"
