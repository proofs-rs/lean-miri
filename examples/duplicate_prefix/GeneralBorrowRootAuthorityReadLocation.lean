import duplicate_prefix.GeneralBorrowRootAuthorityReadEvents
import duplicate_prefix.GeneralBorrowProtectedReadSingleRoot
namespace DuplicatePrefix.GeneralBorrowRootAuthorityReadLocation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowEvents BorrowRangeAccess
open GeneralBorrowProjection GeneralBorrowExposure GeneralBorrowStructuralHistoryRootAuthorityAt GeneralBorrowRootAuthorityReadEvents
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A Read through a descendant treats its owning ancestor root locally.
Every actual callback retains latent root Write permission; other present
states remain possible and absent slots remain physically Clean. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root anchor : UniIndex) (rootNode anchorNode : TreeNode)
    (rootPresent : tree.nodeAt root=some rootNode) (anchorPresent : tree.nodeAt anchor=some anchorNode)
    (mode : ChildrenVisitMode) (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (fits : tree.nodes.data.size≤4294967296) (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (ancestor : root.toNat∈(source_normal_projection tree location protections).topology.ancestorPath anchor.toNat)
    (readable : GeneralBorrowPhysicalReadable.Profile tree location protections) (initial : At tree location root) :
    (tree.performNormalAccessAt location anchor .Read protections mode).access.status=.Completed ∧
    (tree.performNormalAccessAt location anchor .Read protections mode).outcome=.ok () ∧
    At tree (tree.performNormalAccessAt location anchor .Read protections mode).location root := by
  have physical := GeneralBorrowPhysicalReadable.normal tree location protections anchor mode forest fits depth children anchorNode anchorPresent readable
  have valid : anchor.toNat<(source_normal_projection tree location protections).topology.nodes.size := by
    obtain ⟨valid,_⟩:=array_of_node tree anchor anchorNode anchorPresent
    unfold_general_projection;unfold_general_topology
    simpa only[Array.size_mapIdx,Array.size_map] using valid
  have schedule := GeneralBorrowTraversal.traversal_data (source_normal_projection tree location protections).topology forest anchor.toNat valid mode
    (sourceNormalSkipped (source_normal_projection tree location protections) .Read)
  have oldRoot : RootOwned (source_normal_projection tree location protections) root.toNat := by
    intro state found
    rw[projection_location_state tree location protections root rootNode rootPresent] at found
    have equal : state=(location.perms.get root).getD rootNode.defaultLocationState := by
      apply Option.some.inj
      simpa [BorrowTree.locationStateAt,rootPresent] using found.symm
    rw[equal]
    simpa only[Allowed,GeneralBorrowGcPartitionOwnership.Allowed,ite_true] using initial.present root rootNode rootPresent
  have rootFrame := GeneralBorrowRootAuthorityReadEvents.events
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).2
    ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) .Read)).1
    root.toNat (source_normal_projection tree location protections)
    (by
      intro event member same
      have related := (schedule.2 event member).2
      rw[same] at related
      simpa only[ancestor,ite_true] using related)
    oldRoot
  change RootOwned ((source_normal_projection tree location protections).performAccess anchor.toNat .Read mode).tree root.toNat at rootFrame
  rw[←GeneralBorrowRangePreserves.normal_projection tree location protections anchor .Read mode fits] at rootFrame
  refine ⟨physical.1,physical.2.1,?_,physical.2.2.vacant⟩
  intro query node present
  by_cases same : query=root
  · subst query
    have equal : node=rootNode := Option.some.inj (present.symm.trans rootPresent)
    subst node
    simp only[Allowed,GeneralBorrowGcPartitionOwnership.Allowed,ite_true]
    apply rootFrame
    rw[projection_location_state tree _ protections root rootNode rootPresent]
    simp [BorrowTree.locationStateAt,rootPresent]
  · simp only[Allowed,GeneralBorrowGcPartitionOwnership.Allowed,same,ite_false]
    exact (physical.2.2.present query node present).1

/-- Single-root graph data derives the owning ancestor relation, then the
actual full per-location source callback retains latent authority. This is the
callback used by the real implicit Read on protector release. -/
theorem single_root (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root anchor : UniIndex) (rootNode anchorNode : TreeNode)
    (rootPresent : tree.nodeAt root=some rootNode) (anchorPresent : tree.nodeAt anchor=some anchorNode)
    (mode : ChildrenVisitMode) (range : ByteRange)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (fits : tree.nodes.data.size≤4294967296) (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (roots : tree.roots=#[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (readable : GeneralBorrowPhysicalReadable.Profile tree location protections) (initial : At tree location root) :
    source_access_status (source_tree_access_at tree location (some anchor) .Read protections mode range)=none ∧
      At tree (source_access_location (source_tree_access_at tree location (some anchor) .Read protections mode range)) root := by
  have valid : anchor.toNat<(source_normal_projection tree location protections).topology.nodes.size := by
    obtain ⟨valid,_⟩:=array_of_node tree anchor anchorNode anchorPresent
    unfold_general_projection;unfold_general_topology
    simpa only[Array.size_mapIdx,Array.size_map] using valid
  have pathRoot := GeneralBorrowTerminal.ancestor_root_present (source_normal_projection tree location protections).topology forest
    (GeneralBorrowGraph.Present tree) (GeneralBorrowGraph.parents_closed tree location protections depth) anchor.toNat root.toNat valid
    ⟨anchor,anchorNode,rfl,anchorPresent⟩
    (fun index _ present parentless=>GeneralBorrowGraph.unique_root tree location protections root roots covered index present parentless)
  have nonempty : (source_normal_projection tree location protections).topology.ancestorPath anchor.toNat≠[] :=
    GeneralBorrowTerminal.ancestors_nonempty (source_normal_projection tree location protections).topology
      (source_normal_projection tree location protections).topology.nodes.size anchor.toNat
  have ancestor : root.toNat∈(source_normal_projection tree location protections).topology.ancestorPath anchor.toNat := by
    rw[←pathRoot,List.getLast!_eq_getLast?_getD,List.getLast?_eq_some_getLast nonempty]
    exact List.getLast_mem nonempty
  have compatible := GeneralBorrowPhysicalReadable.compatible tree location protections anchor anchorNode anchorPresent depth fits readable
  have preserved := normal tree location protections root anchor rootNode anchorNode rootPresent anchorPresent mode forest fits depth children ancestor readable initial
  refine ⟨GeneralBorrowProtectedReadSingleRoot.access_at tree location protections anchor root mode range forest valid compatible depth children anchorNode anchorPresent roots covered,?_⟩
  rw[GeneralBorrowProtectedReadSingleRoot.single_root_location tree location protections anchor root mode range forest valid compatible depth children anchorNode anchorPresent roots covered]
  exact preserved.2.2
end DuplicatePrefix.GeneralBorrowRootAuthorityReadLocation
