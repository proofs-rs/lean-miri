import duplicate_prefix.GeneralBorrowFrontier
import duplicate_prefix.GeneralBorrowAnchor
namespace DuplicatePrefix.GeneralBorrowTraversal
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowTopology DuplicatePrefix.GeneralBorrowForest DuplicatePrefix.GeneralBorrowFrontier
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem traversal_data (tree : TraversalTree) (forest : Forest tree) (anchor : Nat)
    (valid : anchor < tree.nodes.size) (mode : ChildrenVisitMode) (skips : List Nat) :
    ((tree.traverse anchor mode skips).2.map TraversalEvent.node).Nodup ∧
    ∀ event ∈ (tree.traverse anchor mode skips).2,
      event.node < tree.nodes.size ∧ event.relatedness =
        (if event.node ∈ tree.ancestorPath anchor then .LocalAccess else .ForeignAccess) := by
  let path := tree.ancestorPath anchor
  let roots := sourceForeignRoots tree path mode
  let foreignEvents := roots.flatMap (sourceForeignPostorder tree skips tree.nodes.size)
  have pathData := ancestors_data tree forest.rank forest.parents tree.nodes.size anchor valid
  have rootData : FrontierData tree path none roots := initial_roots_data tree forest anchor valid mode
  have foreignData : ∀ event ∈ foreignEvents, event.relatedness = .ForeignAccess ∧
      event.node < tree.nodes.size ∧ event.node ∉ path := by
    intro event member
    obtain ⟨root,rootMember,inRoot⟩ := List.mem_flatMap.mp member
    have descendant := foreign_desc tree forest skips tree.nodes.size root
      (rootData.bounded root rootMember) event inRoot
    exact ⟨(foreign_events_data tree skips tree.nodes.size root event inRoot).1,descendant.valid.2,
      fun localNode => rootData.offPath root rootMember event.node localNode descendant⟩
  have foreignDistinct : (foreignEvents.map TraversalEvent.node).Nodup := by
    dsimp only [foreignEvents]
    rw [List.map_flatMap]
    apply List.pairwise_flatMap.mpr
    constructor
    · intro root member
      exact foreign_nodes_nodup tree forest skips tree.nodes.size root (rootData.bounded root member)
    · apply rootData.separate.imp_of_mem
      intro left right leftMember rightMember separate leftNode inLeft rightNode inRight same
      obtain ⟨leftEvent,leftIn,leftEq⟩ := List.mem_map.mp inLeft
      obtain ⟨rightEvent,rightIn,rightEq⟩ := List.mem_map.mp inRight
      have leftDesc := foreign_desc tree forest skips tree.nodes.size left
        (rootData.bounded left leftMember) leftEvent leftIn
      have rightDesc := foreign_desc tree forest skips tree.nodes.size right
        (rootData.bounded right rightMember) rightEvent rightIn
      have sameNode : leftEvent.node = rightEvent.node := leftEq.trans (same.trans rightEq.symm)
      exact separate leftEvent.node ⟨leftDesc,by rw [sameNode]; exact rightDesc⟩
  change ((path.map (fun index => (⟨index,.LocalAccess⟩ : TraversalEvent)) ++ foreignEvents).map
    TraversalEvent.node).Nodup ∧ _
  constructor
  · simp only [List.map_append,List.map_map,Function.comp_def]
    apply List.nodup_append.mpr
    refine ⟨by simpa [path,TraversalTree.ancestorPath] using pathData.1,foreignDistinct,?_⟩
    intro localNode localMember other otherMember same
    obtain ⟨event,inForeign,eventEq⟩ := List.mem_map.mp otherMember
    have outside := (foreignData event inForeign).2.2
    apply outside
    rw [eventEq,←same]
    simpa using localMember
  · intro event member
    change event ∈ path.map (fun index => (⟨index,.LocalAccess⟩ : TraversalEvent)) ++ foreignEvents at member
    rcases List.mem_append.mp member with localEvent | foreignEvent
    · obtain ⟨node,nodeMember,eventEq⟩ := List.mem_map.mp localEvent
      subst event
      exact ⟨(pathData.2 node nodeMember).1,by simp [path] at nodeMember ⊢; exact nodeMember⟩
    · have data := foreignData event foreignEvent
      have outside : event.node ∉ tree.ancestorPath anchor := data.2.2
      exact ⟨data.2.1,by simpa only [ite_eq_right outside] using data.1⟩

/-- Actual source normal-tree access under a ranked reciprocal forest and
pointwise anchor ownership. All visitor and cache conditions are derived. -/
theorem normal_access (tree : NormalTreeState) (forest : Forest tree.topology)
    (anchor : Nat) (kind : AccessKind) (mode : ChildrenVisitMode)
    (owned : GeneralBorrowAnchor.AnchorOwned tree anchor kind) :
    (tree.performAccess anchor kind mode).status = .Completed := by
  have schedule := traversal_data tree.topology forest anchor owned.anchorValid mode (sourceNormalSkipped tree kind)
  exact GeneralBorrowAnchor.normal_access_of_anchor tree anchor kind mode owned schedule.1 schedule.2
end DuplicatePrefix.GeneralBorrowTraversal

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowTraversal." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general traversal dependency {dependency}"
