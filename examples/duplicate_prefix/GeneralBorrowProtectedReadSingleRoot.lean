import duplicate_prefix.GeneralBorrowProtectedReadLocation
import duplicate_prefix.GeneralBorrowSingleRoot
namespace DuplicatePrefix.GeneralBorrowProtectedReadSingleRoot
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
private theorem none_choice (condition : Prop) [Decidable condition] (location : LocationTree) :
    (ForInStep.value (if condition then ForInStep.yield (location,(none : Option BorrowTree.BorrowTreeAccessStatus),true)
      else ForInStep.yield (location,none,false))).2.1 = none := by
  by_cases chosen : condition <;> simp [chosen,ForInStep.value]

theorem access_at_path (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor root : UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size)
    (initial : ∀ index,index < (source_normal_projection tree location protections).topology.nodes.size → ∃ state,
      (source_normal_projection tree location protections).stateAt index = some state ∧
      GeneralBorrowProtectedReadCompatible.Compatible state
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
        ((source_normal_projection tree location protections).protectedNodes.contains index))
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root])
    (rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = root.toNat) :
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections mode range) = none := by
  have succeeded := GeneralBorrowProtectedReadLocation.normal_succeeds tree location protections anchor mode
    forest valid initial depth children anchorNode anchorPresent
  have normalRoot : (tree.performNormalAccessAt location anchor .Read protections mode).access.root = root.toNat := by
    exact (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree location protections)).trans rootPath
  have converted : UniIndex.ofNat? (tree.performNormalAccessAt location anchor .Read protections mode).access.root = some root := by
    rw [normalRoot]
    exact index_self root
  simp_tree_helpers
  simp only [succeeded.1,succeeded.2,converted]
  simp [roots,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    List.range'_succ,List.range'_zero,bind,pure]
  change (ForInStep.value (_ : ForInStep (LocationTree × Option BorrowTree.BorrowTreeAccessStatus × Bool))).2.1 = none
  exact none_choice _ _
/-- Full real per-location concrete-tree access for an arbitrary single-root
allocation history. Root coverage, topology and ownership are data invariants;
no successful borrow operation is supplied as a premise. -/
theorem access_at (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor root : UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size)
    (initial : ∀ index,index < (source_normal_projection tree location protections).topology.nodes.size → ∃ state,
      (source_normal_projection tree location protections).stateAt index = some state ∧
      GeneralBorrowProtectedReadCompatible.Compatible state
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
        ((source_normal_projection tree location protections).protectedNodes.contains index))
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree) :
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections mode range) = none := by
  have pathRoot := GeneralBorrowTerminal.ancestor_root_present
    (source_normal_projection tree location protections).topology forest (GeneralBorrowGraph.Present tree)
    (GeneralBorrowGraph.parents_closed tree location protections depth) anchor.toNat root.toNat valid
    ⟨anchor,anchorNode,rfl,anchorPresent⟩
    (fun index _ present parentless => GeneralBorrowGraph.unique_root tree location protections root roots covered index present parentless)
  exact access_at_path tree location protections anchor root mode range forest valid initial depth children anchorNode anchorPresent roots pathRoot

private theorem location_choice (condition : Prop) [Decidable condition] (location : LocationTree) :
    (ForInStep.value (if condition then ForInStep.yield (location,(none : Option BorrowTree.BorrowTreeAccessStatus),true)
      else ForInStep.yield (location,none,false))).1 = location := by
  by_cases chosen : condition <;> simp [chosen,ForInStep.value]

theorem single_root_location (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor root : UniIndex) (mode : ChildrenVisitMode) (range : ByteRange)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (valid : anchor.toNat < (source_normal_projection tree location protections).topology.nodes.size)
    (initial : ∀ index,index < (source_normal_projection tree location protections).topology.nodes.size → ∃ state,
      (source_normal_projection tree location protections).stateAt index = some state ∧
      GeneralBorrowProtectedReadCompatible.Compatible state
        (GeneralBorrowAnchor.relation (source_normal_projection tree location protections) anchor.toNat index)
        ((source_normal_projection tree location protections).protectedNodes.contains index))
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree) :
    source_access_location (source_tree_access_at tree location (some anchor) .Read protections mode range) =
      (tree.performNormalAccessAt location anchor .Read protections mode).location := by
  have succeeded := GeneralBorrowProtectedReadLocation.normal_succeeds tree location protections anchor mode
    forest valid initial depth children anchorNode anchorPresent
  have pathRoot := GeneralBorrowTerminal.ancestor_root_present
    (source_normal_projection tree location protections).topology forest (GeneralBorrowGraph.Present tree)
    (GeneralBorrowGraph.parents_closed tree location protections depth) anchor.toNat root.toNat valid
    ⟨anchor,anchorNode,rfl,anchorPresent⟩
    (fun index _ present parentless => GeneralBorrowGraph.unique_root tree location protections root roots covered index present parentless)
  have normalRoot : (tree.performNormalAccessAt location anchor .Read protections mode).access.root = root.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree location protections)).trans pathRoot
  have converted : UniIndex.ofNat? (tree.performNormalAccessAt location anchor .Read protections mode).access.root = some root := by
    rw [normalRoot]
    exact index_self root
  simp_tree_helpers
  simp only [succeeded.1,succeeded.2,converted]
  simp [roots,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    List.range'_succ,List.range'_zero,bind,pure]
  change (ForInStep.value (_ : ForInStep (LocationTree × Option BorrowTree.BorrowTreeAccessStatus × Bool))).1 = _
  exact location_choice _ _


end DuplicatePrefix.GeneralBorrowProtectedReadSingleRoot
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadSingleRoot.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected Read single-root dependency {dependency}"
