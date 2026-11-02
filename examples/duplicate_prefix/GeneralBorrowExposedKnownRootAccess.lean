import duplicate_prefix.GeneralBorrowExposedKnownRootSchedule
import duplicate_prefix.GeneralBorrowExposedKnownRootMinimum
import duplicate_prefix.GeneralBorrowExposedKnownRootTransport
namespace DuplicatePrefix.GeneralBorrowExposedKnownRootAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState
open GeneralBorrowExposedNonleafState (ReadFrame)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

open Lean Elab in
elab "known_root_scanAt" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposedConcreteLast.scanAt" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected source-bound selected-root callback"
open Lean Elab in
elab "known_root_indexed" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposedConcreteLast.indexed" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected source-bound selected-root index adapter"

private theorem iterator (tree : BorrowTree) (before middle after : LocationTree) (anchor selected head : UniIndex)
    (selectedNode : TreeNode) (tail : List UniIndex) (protections : ProtectedTags) (mode : ChildrenVisitMode) (range : ByteRange)
    (roots : tree.roots = (head::tail).toArray) (present : tree.nodes.get selected = some selectedNode)
    (normalStatus : (tree.performNormalAccessAt before anchor .Read protections mode).access.status = .Completed)
    (normalOutcome : (tree.performNormalAccessAt before anchor .Read protections mode).outcome = .ok ())
    (rootEq : (tree.performNormalAccessAt before anchor .Read protections mode).access.root = selected.toNat)
    (minimum : source_min_exposed tree anchor = none)
    (first : (if selected = head then ⟨(tree.performNormalAccessAt before anchor .Read protections mode).location,.Completed⟩
      else tree.performWildcardAccessAt (tree.performNormalAccessAt before anchor .Read protections mode).location head
        (some selectedNode.tag) .Read protections false) = (⟨middle,.Completed⟩ : BorrowTree.WildcardLocationAccessResult))
    (completed : GeneralBorrowExposedKnownRootSchedule.run tree tail selected middle selectedNode.tag protections = ⟨after,.Completed⟩) :
    source_access_location (source_tree_access_at tree before (some anchor) .Read protections mode range) = after ∧
    source_access_status (source_tree_access_at tree before (some anchor) .Read protections mode range) = none := by
  simp_tree_helpers
  simp only [normalStatus,normalOutcome,rootEq,index_self,present,roots]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one,
    List.size_toArray,List.length_cons]
  by_cases same : selected = head
  · subst selected
    have equal : (tree.performNormalAccessAt before anchor .Read protections mode).location = middle := by
      simpa only [ite_true] using congrArg BorrowTree.WildcardLocationAccessResult.location first
    simp [present,minimum,List.size_toArray,List.range'_succ,bind,pure,equal]
    change (forIn (List.range' 1 tail.length) (middle,none,false)
      (known_root_scanAt tree head head tail selectedNode.tag .Read protections range)).1 = after ∧
      (forIn (List.range' 1 tail.length) (middle,none,false)
      (known_root_scanAt tree head head tail selectedNode.tag .Read protections range)).2.1 = none
    rw [known_root_indexed,GeneralBorrowExposedKnownRootSchedule.successful tree tail head middle after selectedNode.tag protections range completed]
    exact ⟨rfl,rfl⟩
  · have called : tree.performWildcardAccessAt (tree.performNormalAccessAt before anchor .Read protections mode).location head
        (some selectedNode.tag) .Read protections false = ⟨middle,.Completed⟩ := by simpa only [same,ite_false] using first
    simp [present,minimum,List.size_toArray,List.range'_succ,bind,pure,same,called]
    change (forIn (List.range' 1 tail.length) (middle,none,false)
      (known_root_scanAt tree head selected tail selectedNode.tag .Read protections range)).1 = after ∧
      (forIn (List.range' 1 tail.length) (middle,none,false)
      (known_root_scanAt tree head selected tail selectedNode.tag .Read protections range)).2.1 = none
    rw [known_root_indexed,GeneralBorrowExposedKnownRootSchedule.successful tree tail selected middle after selectedNode.tag protections range completed]
    exact ⟨rfl,rfl⟩

/-- A concrete normal prefix in its own hidden component followed by actual
conditional exposed nonleaf accesses across every other ordered root. The
selected root may occupy any array position. All permissions are component
scoped; an active hidden protected Unique selected node is permitted. Root zero,
when different, carries its own exposed supporting descendant. Raw tag bounds
make the real SOME cutoff inert; hidden child closure derives the skip-mode
minimum search result. No visited-success or callback-classification premise is supplied. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (anchorNode selectedNode : TreeNode) (tail : List UniIndex)
    (mode : ChildrenVisitMode) (range : ByteRange)
    (roots : tree.roots = (head::tail).toArray)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat)
    (owned : GeneralBorrowExposedScopedNormal.Owned (source_normal_projection tree location protections) anchor.toNat .Read component)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorPresent : tree.nodeAt anchor = some anchorNode) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = selected.toNat)
    (hidden : ∀ index node,component.support index.toNat → tree.nodeAt index = some node → node.isExposed = false)
    (separate : ∀ index,area.support index → ¬component.support index.toNat)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (readable : Readable tree location protections)
    (tags : ∀ index node,area.support index → tree.nodes.get index = some node → node.tag.value ≤ selectedNode.tag.value)
    (primaryData : head ≠ selected → GeneralBorrowExposedKnownRootPrimaryWitness.Data tree location head protections)
    (tailData : ∀ root ∈ tail,root ≠ selected → Data tree location root protections) :
    ∃ after,
      source_access_location (source_tree_access_at tree location (some anchor) .Read protections mode range) = after ∧
      source_access_status (source_tree_access_at tree location (some anchor) .Read protections mode range) = none ∧
      ReadFrame location after ∧ Readable tree after protections ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections := by
  have normal := GeneralBorrowExposedScopedNormalCache.access tree location protections anchor .Read mode forest component owned depth children anchorNode anchorPresent hidden coherent
  let normalLocation := (tree.performNormalAccessAt location anchor .Read protections mode).location
  have outside : ∀ index node,area.support index → tree.nodes.get index = some node → normalLocation.perms.get index = location.perms.get index := by
    intro index node member present
    exact normal.2.2.2.2 index node present (separate index member)
  have normalReadable := GeneralBorrowExposedKnownRootTransport.readable tree location normalLocation protections normal.2.2.1 outside readable
  have rootEq : (tree.performNormalAccessAt location anchor .Read protections mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree location protections)).trans rootPath
  have childClosed : ∀ index node,component.support index.toNat → tree.nodes.get index = some node →
      ∀ child ∈ node.children.toList,component.support child.toNat := by
    intro index node member present child childMember
    apply component.children index.toNat member child.toNat
    change child.toNat ∈ ((source_normal_projection tree location protections).topology.nodes[index.toNat]?.getD ⟨none,[]⟩).children
    rw [projection_topology_node tree location protections index.toNat index node rfl present]
    exact List.mem_map.mpr ⟨child,childMember,rfl⟩
  have minimum := GeneralBorrowExposedKnownRootMinimum.min_none tree anchor (fun index => component.support index.toNat) component.anchor childClosed hidden
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree location protections forest
  have bound := GeneralBorrowWildcardForestWeights.bounded tree location protections forest
  let first : BorrowTree.WildcardLocationAccessResult := if selected = head then ⟨normalLocation,.Completed⟩
    else tree.performWildcardAccessAt normalLocation head (some selectedNode.tag) .Read protections false
  have firstGood : first.status = .Completed ∧ ReadFrame normalLocation first.location ∧ Readable tree first.location protections ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree first.location protections := by
    by_cases same : selected = head
    · simp only [first,same,ite_true]
      exact ⟨True.intro,fun _ => rfl,normalReadable,normal.2.2.2.1⟩
    · let data := GeneralBorrowExposedKnownRootTransport.primary (primaryData (Ne.symm same)) normalLocation normal.2.2.2.1 normalReadable outside
      simpa only [first,same,ite_false] using GeneralBorrowExposedKnownRootPrimaryLoop.access tree normalLocation head selectedNode.tag protections weights (bound head) data tags
  have data : ∀ root ∈ tail,root ≠ selected → Data tree normalLocation root protections := by
    intro root member different
    exact GeneralBorrowExposedKnownRootTransport.rebase (tailData root member different) normalLocation normal.2.2.2.1 normalReadable
  obtain ⟨after,completed,frame,profile,finalCoherent⟩ := GeneralBorrowExposedKnownRootSchedule.fold_from tree normalLocation first.location protections tail selected
    selectedNode.tag weights (fun root _ => bound root) data firstGood.2.1 firstGood.2.2.1 firstGood.2.2.2 tags
  have firstEq : first = ⟨first.location,.Completed⟩ := by
    have reconstruct : first = ⟨first.location,first.status⟩ := by cases first;rfl
    rw [firstGood.1] at reconstruct
    exact reconstruct
  obtain ⟨actual,status⟩ := iterator tree location first.location after anchor selected head selectedNode tail protections mode range roots selectedPresent
    normal.1 normal.2.1 rootEq minimum firstEq completed
  refine ⟨after,actual,status,?_,profile,finalCoherent⟩
  intro query
  exact (frame query).trans (by rw [show normalLocation.exposedCache = location.exposedCache from normal.2.2.1])
end DuplicatePrefix.GeneralBorrowExposedKnownRootAccess
