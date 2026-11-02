import duplicate_prefix.GeneralBorrowExposedScopedMixedClosedData
namespace DuplicatePrefix.GeneralBorrowExposedScopedLeafReadFrame
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState
open GeneralBorrowExposedScopedMixedRangeData (Data)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

open Lean Elab in
elab "scoped_leaf_physical" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposedConcreteLast.physical" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected pinned supporting-leaf physical source proof"
open Lean Elab in
elab "scoped_leaf_iterator" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposedScopedReadFrameAccess.iterator" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected pinned selected-component source iterator proof"

/-- Supporting old leaves are true no-ops in every other physical root call.
The actual whole concrete Read therefore changes precisely its selected normal
component, including permission write-back and the real root-array dispatcher. -/
theorem normal_only (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (tail : List UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (support : Nat → Prop) (writable : Nat → Bool)
    (data : Data tree location protections anchor selected head tail support writable)
    (short : tree.nodes.size < 65536)
    (leafs : ∀ index,area.support index → ∃ node,tree.nodeAt index = some node ∧ node.children = #[] ∧
      node.isExposed = true ∧ location.perms.get index = some GeneralBorrowWildcardLeaf.unique) :
    source_access_location (source_tree_access_at tree location (some anchor) .Read protections mode range) =
      (tree.performNormalAccessAt location anchor .Read protections mode).location ∧
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections mode range) = none := by
  let normalLocation := (tree.performNormalAccessAt location anchor .Read protections mode).location
  have normal := GeneralBorrowExposedScopedNormalCache.access tree location protections anchor .Read mode data.base.forest
    data.base.component data.base.owned context.depth context.children context.anchorNode context.anchorPresent data.base.hidden data.base.coherent
  have leaves : ∀ query,area.support query → ∃ node,tree.nodeAt query = some node ∧ node.children = #[] ∧
      node.isExposed = true ∧ normalLocation.perms.get query = some GeneralBorrowWildcardLeaf.unique := by
    intro query included
    obtain ⟨node,present,leaf,exposed,stored⟩ := leafs query included
    exact ⟨node,present,leaf,exposed,(normal.2.2.2.2 query node present (data.base.separate query included)).trans stored⟩
  have positive : ∀ query node,tree.nodeAt query = some node → node.isExposed = true →
      normalLocation.perms.get query = some GeneralBorrowWildcardLeaf.unique →
      GeneralBorrowWildcardRelatednessBounds.count normalLocation.exposedCache query .Read ≠ 0 := by
    intro query node present exposed stored
    have supports : GeneralBorrowExposureCardinality.supports
        (GeneralBorrowExposureCardinality.effective normalLocation protections query node) .Read = true := by
      simp [GeneralBorrowExposureCardinality.effective,stored,GeneralBorrowWildcardLeaf.unique,Permission.strongestAllowedLocalAccess,
        GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsRead]
    have bounded := GeneralBorrowExposureCardinality.exposed_self normalLocation.exposedCache tree.nodes
      (GeneralBorrowExposureCardinality.effective normalLocation protections) normal.2.2.2.1
      short query node present exposed .Read supports
    exact Nat.ne_of_gt bounded
  have first : (if selected = head then ⟨normalLocation,.Completed⟩ else
      tree.performWildcardAccessAt normalLocation head (some context.selectedNode.tag) .Read protections false) =
      (⟨normalLocation,.Completed⟩ : BorrowTree.WildcardLocationAccessResult) := by
    by_cases same : selected = head
    · simp only [same,ite_true]
    · have initial := data.base.primary (Ne.symm same)
      have included := initial.base.included head initial.base.rooted
      obtain ⟨node,present,leaf,exposed,stored⟩ := leaves head included
      simpa only [same,ite_false] using scoped_leaf_physical tree normalLocation head node context.selectedNode.tag .Read protections
        present leaf exposed stored (context.tags head node included present) (positive head node present exposed stored)
  have completed : GeneralBorrowExposedKnownRootSchedule.run tree tail selected normalLocation context.selectedNode.tag protections =
      ⟨normalLocation,.Completed⟩ := by
    have all : ∀ roots : List UniIndex, (∀ root ∈ roots,root ∈ tail) →
        GeneralBorrowExposedKnownRootSchedule.run tree roots selected normalLocation context.selectedNode.tag protections = ⟨normalLocation,.Completed⟩ := by
      intro roots
      induction roots with
      | nil => intro subset;rfl
      | cons root rest ih =>
        intro subset
        by_cases same : root = selected
        · simpa only [GeneralBorrowExposedKnownRootSchedule.run,same,ite_true] using ih (fun query member => subset query (by simp [member]))
        · let initial := data.base.virtual root (subset root (by simp)) same
          have included := initial.included root initial.rooted
          obtain ⟨node,present,leaf,exposed,stored⟩ := leaves root included
          have cutoff : GeneralBorrowWildcardVirtualLeaf.onlyForeign node (some context.selectedNode.tag) = false := by
            simp only [GeneralBorrowWildcardVirtualLeaf.onlyForeign]
            exact decide_eq_false (UInt64.not_lt.mpr (context.tags root node included present))
          have called := GeneralBorrowWildcardVirtualLeaf.either_access tree normalLocation root node (some context.selectedNode.tag) .Read protections
            present leaf (positive root node present exposed stored) cutoff
          have materialized : GeneralBorrowWildcardVirtualLeaf.materialized normalLocation root node = normalLocation := by
            simp only [GeneralBorrowWildcardVirtualLeaf.materialized,UniValMap.orInsert,stored]
          rw [materialized] at called
          simpa only [GeneralBorrowExposedKnownRootSchedule.run,same,ite_false,called,beq_self_eq_true,ite_true] using
            ih (fun query member => subset query (by simp [member]))
    exact all tail (fun _ member => member)
  have childClosed : ∀ index node,data.base.component.support index.toNat → tree.nodes.get index = some node →
      ∀ child ∈ node.children.toList,data.base.component.support child.toNat := by
    intro index node member present child childMember
    apply data.base.component.children index.toNat member child.toNat
    change child.toNat ∈ ((source_normal_projection tree location protections).topology.nodes[index.toNat]?.getD ⟨none,[]⟩).children
    rw [projection_topology_node tree location protections index.toNat index node rfl present]
    exact List.mem_map.mpr ⟨child,childMember,rfl⟩
  have minimum := GeneralBorrowExposedKnownRootMinimum.min_none tree anchor (fun index => data.base.component.support index.toNat)
    data.base.component.anchor childClosed data.base.hidden
  have rootEq : (tree.performNormalAccessAt location anchor .Read protections mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree location protections)).trans data.base.rootPath
  exact scoped_leaf_iterator tree location normalLocation normalLocation anchor selected head context.selectedNode tail protections mode range
    context.roots context.selectedPresent normal.1 normal.2.1 rootEq minimum first completed
end DuplicatePrefix.GeneralBorrowExposedScopedLeafReadFrame
