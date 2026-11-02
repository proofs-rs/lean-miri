import duplicate_prefix.GeneralBorrowProtectedReadProfile
import duplicate_prefix.GeneralBorrowLocationSifaConsistency
import duplicate_prefix.GeneralBorrowParentlessTraversal
namespace DuplicatePrefix.GeneralBorrowProtectedChildReadSchedule
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowEvents DuplicatePrefix.GeneralBorrowFrontier DuplicatePrefix.GeneralBorrowTopology
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- An immediate foreign child with a formed protected unconflicted
reservation cannot be pruned by an ancestor: its root has a one-node local
path, and its own real skip predicate must recurse. Arbitrary descendant and
other sibling subtrees are allowed. -/
theorem direct_child (tree : NormalTreeState) (forest : GeneralBorrowForest.Forest tree.topology)
    (root child : Nat) (rootValid : root < tree.topology.nodes.size)
    (parentless : tree.topology.nodes[root].parent = none)
    (listed : child ∈ tree.topology.nodes[root].children) (state : LocationState)
    (present : tree.stateAt child = some state) (_held : tree.protectedNodes.contains child = true)
    (reservation : state.permission = .ReservedFrz false)
    (consistent : GeneralBorrowSifaPermissionConsistency.Consistent state true) :
    (⟨child,.ForeignAccess⟩ : TraversalEvent) ∈
      (tree.topology.traverse root .VisitChildrenOfAccessed (sourceNormalSkipped tree .Read)).2 := by
  have childValid := (forest.childParent root rootValid child listed).1
  have path := GeneralBorrowParentlessTraversal.ancestor_path tree.topology root rootValid parentless
  have recurse := (GeneralBorrowSifaPermissionConsistency.reservation_recurse state consistent reservation).2
  have notSkipped : child ∉ sourceNormalSkipped tree .Read := by
    intro member
    have skipped := (GeneralBorrowEvents.skipped_iff tree .Read child state present childValid).mp member
    rw [recurse] at skipped
    cases skipped
  have rootMember : child ∈ sourceForeignRoots tree.topology [root] .VisitChildrenOfAccessed := by
    change child ∈ sourceForeignRootsGo tree.topology .VisitChildrenOfAccessed [root] none true
    rw [roots_cons,roots_nil]
    simp only [deferredHeads,Bool.not_true,Bool.false_or,beq_self_eq_true,ite_true,List.append_nil]
    simpa [GeneralBorrowPresence.nodeData,rootValid,List.mem_reverse] using listed
  have eventMember : (⟨child,.ForeignAccess⟩ : TraversalEvent) ∈
      sourceForeignPostorder tree.topology (sourceNormalSkipped tree .Read) tree.topology.nodes.size child := by
    cases size : tree.topology.nodes.size with
    | zero => omega
    | succ fuel =>
      rw [foreign_succ]
      have notContains : ¬(sourceNormalSkipped tree .Read).contains child = true :=
        fun found => notSkipped (List.contains_iff_mem.mp found)
      rw [ite_eq_right notContains]
      exact List.mem_append_right _ (by simp)
  change (⟨child,.ForeignAccess⟩ : TraversalEvent) ∈
    (tree.topology.ancestorPath root).map (fun index => ⟨index,.LocalAccess⟩) ++
      (sourceForeignRoots tree.topology (tree.topology.ancestorPath root) .VisitChildrenOfAccessed).flatMap
        (sourceForeignPostorder tree.topology (sourceNormalSkipped tree .Read) tree.topology.nodes.size)
  rw [path]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨child,rootMember,eventMember⟩)

/-- The actual normal constructor-leading root Read conflicts an earlier
protected direct child from the formed physical SIFA profile. The graph may
have arbitrary other branches; scheduling and operation completion are proved,
not supplied. The earlier node's reservation and child edge are initial data. -/
theorem root_read (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root earlier : UniIndex) (rootNode earlierNode : TreeNode) (state : LocationState)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (rootPresent : tree.nodeAt root = some rootNode) (parentless : rootNode.parent = none)
    (earlierPresent : tree.nodeAt earlier = some earlierNode) (listed : earlier ∈ rootNode.children)
    (oldPresent : tree.locationStateAt location earlier = some state) (reservation : state.permission = .ReservedFrz false)
    (held : protections.contains earlierNode.tag = true)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) root.toNat .Read)
    (initial : GeneralBorrowLocationSifaConsistency.Profile tree location protections) :
    (tree.performNormalAccessAt location root .Read protections .VisitChildrenOfAccessed).access.status = .Completed ∧
    (tree.performNormalAccessAt location root .Read protections .VisitChildrenOfAccessed).outcome = .ok () ∧
    ∃ next,(tree.performNormalAccessAt location root .Read protections .VisitChildrenOfAccessed).location.perms.get earlier = some next ∧
      next.permission = .ReservedFrz true := by
  let normal := source_normal_projection tree location protections
  have rootValid : root.toNat < normal.topology.nodes.size := owned.anchorValid
  have rootShape : normal.topology.nodes[root.toNat] =
      ⟨rootNode.parent.map UniIndex.toNat,rootNode.children.toList.map UniIndex.toNat⟩ := by
    have shape := projection_topology_node tree location protections root.toNat root rootNode rfl rootPresent
    change normal.topology.nodes[root.toNat]?.getD _ = _ at shape
    simpa only [Array.getElem?_eq_getElem rootValid,Option.getD_some] using shape
  have noParent : normal.topology.nodes[root.toNat].parent = none := by
    rw [rootShape,parentless];rfl
  have childMember : earlier.toNat ∈ normal.topology.nodes[root.toNat].children := by
    rw [rootShape]
    exact List.mem_map.mpr ⟨earlier,Array.mem_def.mp listed,rfl⟩
  have rawState : normal.stateAt earlier.toNat = some state := by
    rw [projection_location_state tree location protections earlier earlierNode earlierPresent]
    exact oldPresent
  have protection : normal.protectedNodes.contains earlier.toNat = true :=
    (GeneralBorrowNormalPermissionMetadata.held tree location protections earlier earlierNode earlierPresent).trans held
  have consistent := GeneralBorrowLocationSifaConsistency.projection tree location protections fits initial earlier.toNat state rawState
  rw [protection] at consistent
  have scheduled := direct_child normal forest root.toNat earlier.toNat rootValid noParent childMember state rawState protection reservation consistent
  exact GeneralBorrowProtectedReadProfile.foreign_reservation tree location protections root earlier rootNode earlierNode state false
    depth children rootPresent earlierPresent oldPresent reservation held forest owned scheduled

end DuplicatePrefix.GeneralBorrowProtectedChildReadSchedule
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedChildReadSchedule.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected direct-child Read scheduling dependency {dependency}"
