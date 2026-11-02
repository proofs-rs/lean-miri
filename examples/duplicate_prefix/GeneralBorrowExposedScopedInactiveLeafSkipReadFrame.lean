import duplicate_prefix.GeneralBorrowExposedScopedReadFrameAccess
import duplicate_prefix.GeneralBorrowExposedScopedInactiveExposurePermission
import duplicate_prefix.GeneralBorrowExposedScopedReadFrameSchedule
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveLeafSkipReadFrame
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowExposedKnownRootState
open GeneralBorrowExposedNonleafState (ReadFrame)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
open Lean Elab in
elab "inactive_leaf_skip_iterator" : term => do
  let names := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".GeneralBorrowExposedScopedReadFrameAccess.iterator" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected fixed concrete VisitChildren iterator"

/-- Concrete Read with exposed Unique ancestors retains every selected-component
permission slot after the actual ordered nonleaf callbacks at other roots. -/
theorem access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor selected head : UniIndex) (anchorNode selectedNode : TreeNode) (tail : List UniIndex)
     (range : ByteRange)
    (roots : tree.roots = (head::tail).toArray)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree location protections).topology anchor.toNat)
    (owned : GeneralBorrowExposedScopedNormal.Owned (source_normal_projection tree location protections) anchor.toNat .Read component)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorPresent : tree.nodeAt anchor = some anchorNode) (selectedPresent : tree.nodes.get selected = some selectedNode)
    (leaf : anchorNode.children=#[]) (anchorHidden : anchorNode.isExposed=false)
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = selected.toNat)
    (initialProfile : ∀ index node state,component.support index.toNat → tree.nodeAt index = some node →
      node.isExposed=true → tree.locationStateAt location index=some state →
      (index.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat ∧ state.permission=.Unique) ∨
      (index.toNat ∉ (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat ∧ state.permission=.Disabled))
    (separate : ∀ index,area.support index → ¬component.support index.toNat)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (readable : Readable tree location protections)
    (tags : ∀ index node,area.support index → tree.nodes.get index = some node → node.tag.value ≤ selectedNode.tag.value)
    (primaryData : head ≠ selected → GeneralBorrowExposedKnownRootPrimaryWitness.Data tree location head protections)
    (tailData : ∀ root ∈ tail,root ≠ selected → Data tree location root protections) :
    ∃ after,
      source_access_location (source_tree_access_at tree location (some anchor) .Read protections .SkipChildrenOfAccessed range) = after ∧
      source_access_status (source_tree_access_at tree location (some anchor) .Read protections .SkipChildrenOfAccessed range) = none ∧
      ReadFrame location after ∧ Readable tree after protections ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree after protections ∧
      (∀ query, ¬area.support query → after.perms.get query =
        (tree.performNormalAccessAt location anchor .Read protections .SkipChildrenOfAccessed).location.perms.get query) := by
  have normal := GeneralBorrowExposedScopedInactiveExposureNormal.access tree location protections anchor .Read .SkipChildrenOfAccessed forest component owned depth children anchorNode anchorPresent initialProfile coherent
  let normalLocation := (tree.performNormalAccessAt location anchor .Read protections .SkipChildrenOfAccessed).location
  have outside : ∀ index node,area.support index → tree.nodes.get index = some node → normalLocation.perms.get index = location.perms.get index := by
    intro index node member present
    exact normal.2.2.2.2 index node present (separate index member)
  have normalReadable := GeneralBorrowExposedKnownRootTransport.readable tree location normalLocation protections normal.2.2.1 outside readable
  have rootEq : (tree.performNormalAccessAt location anchor .Read protections .SkipChildrenOfAccessed).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree location protections)).trans rootPath
  have minimum := GeneralBorrowExposedKnownRootMinimum.min_none tree anchor (fun index => index=anchor) rfl
    (by intro index node same present child member;subst index;change tree.nodeAt anchor=some node at present;rw [anchorPresent] at present;cases present;simp only [leaf,Array.toList_empty,List.not_mem_nil] at member)
    (by intro index node same present;subst index;change tree.nodeAt anchor=some node at present;rw [anchorPresent] at present;cases present;exact anchorHidden)
  let weights := GeneralBorrowWildcardForestWeights.of_forest tree location protections forest
  have bound := GeneralBorrowWildcardForestWeights.bounded tree location protections forest
  let first : BorrowTree.WildcardLocationAccessResult := if selected = head then ⟨normalLocation,.Completed⟩
    else tree.performWildcardAccessAt normalLocation head (some selectedNode.tag) .Read protections false
  have firstGood : first.status = .Completed ∧ ReadFrame normalLocation first.location ∧ Readable tree first.location protections ∧
      GeneralBorrowExposureCardinality.LocationCoherent tree first.location protections ∧
      (∀ query, ¬area.support query → first.location.perms.get query = normalLocation.perms.get query) := by
    by_cases same : selected = head
    · simp only [first,same,ite_true]
      exact ⟨True.intro,fun _ => rfl,normalReadable,normal.2.2.2.1,fun _ _ => True.intro⟩
    · let data := GeneralBorrowExposedKnownRootTransport.primary (primaryData (Ne.symm same)) normalLocation normal.2.2.2.1 normalReadable outside
      simpa only [first,same,ite_false] using GeneralBorrowExposedScopedReadFramePrimaryLoop.access tree normalLocation head selectedNode.tag protections weights (bound head) data tags
  have data : ∀ root ∈ tail,root ≠ selected → Data tree normalLocation root protections := by
    intro root member different
    exact GeneralBorrowExposedKnownRootTransport.rebase (tailData root member different) normalLocation normal.2.2.2.1 normalReadable
  obtain ⟨after,completed,frame,profile,finalCoherent,keep⟩ := GeneralBorrowExposedScopedReadFrameSchedule.fold_from tree normalLocation first.location protections tail selected
    selectedNode.tag weights (fun root _ => bound root) data firstGood.2.1 firstGood.2.2.1 firstGood.2.2.2.1 tags
  have firstEq : first = ⟨first.location,.Completed⟩ := by
    have reconstruct : first = ⟨first.location,first.status⟩ := by cases first;rfl
    rw [firstGood.1] at reconstruct
    exact reconstruct
  obtain ⟨actual,status⟩ := inactive_leaf_skip_iterator tree location first.location after anchor selected head selectedNode tail protections .SkipChildrenOfAccessed range roots selectedPresent
    normal.1 normal.2.1 rootEq minimum firstEq completed
  refine ⟨after,actual,status,?_,profile,finalCoherent,fun query outside => (keep query outside).trans (firstGood.2.2.2.2 query outside)⟩
  intro query
  exact (frame query).trans (by rw [show normalLocation.exposedCache = location.exposedCache from normal.2.2.1])
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveLeafSkipReadFrame
