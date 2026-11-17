import duplicate_prefix.WildcardHitPoolRoot
import duplicate_prefix.GeneralBorrowObserverSharedExtension
import duplicate_prefix.GeneralBorrowSharedCallbacksData

namespace DuplicatePrefix.S04ZeroRootObserverNormal
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowPresence GeneralBorrowNodeUpdate GeneralBorrowFreshNode
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

theorem size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.size := by
  unfold_general_projection; unfold_general_topology; simp only [Array.size_map,UniValMap.size]

theorem old_node (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (query : UniIndex) (node : TreeNode) (present : tree.nodeAt query = some node) :
    (slot.after tag).nodeAt query = some node := by
  have different : query ≠ slot.index := by
    intro same
    change tree.nodes.get query = some node at present
    rw [same,slot.vacant] at present
    cases present
  exact (GeneralBorrowFreshLocation.get_other tree.nodes slot.index query _ different).trans present

/-- Isolated-root insertion leaves every projected parent/child pair exactly
unchanged: the fresh parentless leaf has the former vacant/default topology. -/
theorem topology_node (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (location : LocationTree) (protections : ProtectedTags) (position : Nat) :
    nodeData (source_normal_projection (slot.after tag) location protections).topology position =
      nodeData (source_normal_projection tree location protections).topology position := by
  cases slot with
  | append noFree aligned fits =>
    let index : UniIndex := ⟨UInt32.ofNat tree.tagMapping.mapping.size⟩
    have atEnd : index.toNat = tree.nodes.data.size := by
      simp only [index,UniIndex.toNat,UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact aligned
    have insertion := insert_append tree.nodes index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) atEnd
    dsimp only [index] at insertion
    unfold_general_projection
    unfold_general_topology
    simp only [nodeData,WildcardHitPoolRoot.Slot.after,WildcardHitZeroConstructor.installed,
      WildcardHitPoolRoot.Slot.index]
    rw [insertion]
    simp only [Array.map_push,WildcardHitZeroConstructor.rootNode,Option.map_some,Array.toList_empty,List.map_nil]
    simp only [Array.getElem?_push,Array.size_map]
    by_cases equal : position = tree.nodes.data.size
    · subst position
      simp only [ite_true,Option.getD_some,Array.getElem?_map,Array.getElem?_eq_none (Nat.le_refl _),Option.map_none,Option.getD_none]
    · rw [if_neg equal]
  | reuse index available bounded vacant =>
    have missing : tree.nodes.data[index.toNat]'bounded = none := by
      simpa only [UniValMap.get,Array.getElem?_eq_getElem bounded] using vacant
    unfold_general_projection
    unfold_general_topology
    simp only [nodeData,WildcardHitPoolRoot.Slot.after,WildcardHitZeroConstructor.installed,
      WildcardHitPoolRoot.Slot.index,GeneralBorrowFreshReuseNode.insert_bounded tree.nodes index _ bounded,
      Array.map_set,WildcardHitZeroConstructor.rootNode,Option.map_some,Array.toList_empty,List.map_nil]
    by_cases equal : position = index.toNat
    · subst position
      simp [Array.getElem?_set,missing,bounded]
    · simp [Array.getElem?_set,equal,Ne.symm equal]

theorem old_path (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (location : LocationTree) (protections : ProtectedTags)
    (observer : UniIndex) (node : TreeNode) (present : tree.nodeAt observer = some node) :
    (source_normal_projection (slot.after tag) location protections).topology.ancestorPath observer.toNat =
      (source_normal_projection tree location protections).topology.ancestorPath observer.toNat := by
  change sourceAncestorPath _ _ _ = sourceAncestorPath _ _ _
  rw [size,size]
  change sourceAncestorPath (source_normal_projection (slot.after tag) location {}).topology _ _ =
    sourceAncestorPath (source_normal_projection tree location {}).topology _ _
  rw [GeneralBorrowGcAnchorOwnership.path _ (slot.depth depth tag) _ _ observer node (old_node tree slot tag observer node present),
    GeneralBorrowGcAnchorOwnership.path _ depth _ _ observer node present]
  apply congrArg (List.map UniIndex.toNat)
  exact GeneralBorrowExposureGraphTransport.walk_extension tree.nodes (slot.after tag).nodes depth
    (fun query old found => ⟨old,old_node tree slot tag query old found,rfl⟩)
    (tree.nodes.size+1) ((slot.after tag).nodes.size+1) observer node present
    (by have := depth.bounded observer node present;omega)
    (by have := depth.bounded observer node present;rw [slot.size tag];omega)


private def absentDefault : LocationState := ⟨.Disabled,false,.None⟩

private theorem projection_slot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (position : Nat) (query : UniIndex) (converted : UniIndex.ofNat? position = some query)
    (equal : query.toNat = position) (valid : position < tree.nodes.data.size) :
    (source_normal_projection tree location protections).stateAt position =
      some ((location.perms.get query).getD (((tree.nodeAt query).map TreeNode.defaultLocationState).getD absentDefault)) := by
  have nodeValue : tree.nodeAt query = tree.nodes.data[position]'valid := by
    unfold BorrowTree.nodeAt UniValMap.get
    simp only [equal,Array.getElem?_eq_getElem valid]
  unfold_general_projection
  unfold NormalTreeState.stateAt
  simp only [Array.getElem?_mapIdx,Array.getElem?_map,Array.getElem?_eq_getElem valid,
    converted,Option.map_some]
  rw [nodeValue]
  generalize stateEq : location.perms.get query = stored
  clear stateEq
  generalize nodeEq : tree.nodes.data[position] = node
  clear nodeEq
  cases stored <;> cases node <;> rfl


theorem old_bound (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (position : Nat) (bound : position < (slot.after tag).nodes.size) (different : position ≠ slot.index.toNat) :
    position < tree.nodes.size := by
  rw [slot.size tag] at bound
  cases slot with
  | append noFree aligned fits =>
    have atEnd : (WildcardHitPoolRoot.Slot.append noFree aligned fits).index.toNat = tree.nodes.size := by
      simp only [WildcardHitPoolRoot.Slot.index,UniIndex.toNat,UInt32.toNat_ofNat',
        Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact aligned
    simp only [WildcardHitPoolRoot.Slot.growth] at bound
    rw [atEnd] at different
    omega
  | reuse index available bounded vacant => exact bound

theorem foreign_new (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (location : LocationTree) (protections : ProtectedTags)
    (observer : UniIndex) (node : TreeNode) (present : tree.nodeAt observer = some node) :
    GeneralBorrowAnchor.relation (source_normal_projection (slot.after tag) location protections)
      observer.toNat slot.index.toNat = .ForeignAccess := by
  unfold GeneralBorrowAnchor.relation
  rw [old_path tree slot tag depth location protections observer node present]
  apply ite_eq_right
  change slot.index.toNat ∉ sourceAncestorPath (source_normal_projection tree location {}).topology _ observer.toNat
  rw [size,GeneralBorrowGcAnchorOwnership.path tree depth location tree.nodes.size observer node present]
  intro member
  obtain ⟨query,walked,equal⟩ := List.mem_map.mp member
  have same := index_injective query slot.index equal
  subst query
  obtain ⟨⟨value,found⟩,_⟩ := GeneralBorrowExposureAncestorDistinct.present_depth tree.nodes depth
    (tree.nodes.size+1) observer node present slot.index walked
  rw [slot.vacant] at found
  cases found

private theorem protected_old (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (location : LocationTree) (protections : ProtectedTags) (query : UniIndex) (different : query ≠ slot.index) :
    (source_normal_projection (slot.after tag) location protections).protectedNodes.contains query.toNat =
      (source_normal_projection tree location protections).protectedNodes.contains query.toNat := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_iff_mem,GeneralBorrowFreshReuseProtection.protected_iff]
  have lookup : (slot.after tag).nodeAt query = tree.nodeAt query :=
    GeneralBorrowFreshLocation.get_other tree.nodes slot.index query _ different
  rw [lookup]

private theorem reserved_foreign (kind : AccessKind) (held : Bool) :
    DuplicatePrefixScalarAuthorization.Compatible ⟨.ReservedFrz false,false,.None⟩ kind .ForeignAccess held := by
  cases kind <;> cases held <;>
    simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
      GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]

/-- Any old observer retains its entire normal component through the actual
isolated-root insertion. Fresh-index support is harmless: its clean inactive
reservation is foreign to the old observer, with either protection bit. -/
theorem normal (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree) (tag : BorTag)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (location : LocationTree) (protections : ProtectedTags)
    (fits : tree.nodes.size ≤ 4294967296) (clean : location.perms.get slot.index = none)
    (observer : UniIndex) (node : TreeNode) (present : tree.nodeAt observer = some node)
    (old : DuplicatePrefixBorrowAuthorization.Normal tree location protections observer) :
    ∃ next : DuplicatePrefixBorrowAuthorization.Normal (slot.after tag) location protections observer,
      next.component.support = old.component.support := by
  let component : GeneralBorrowExposedScopedNormal.Component
      (source_normal_projection (slot.after tag) default protections).topology observer.toNat := {
    support := old.component.support
    anchor := old.component.anchor
    parents := by
      intro current included parent edge
      rw [topology_node] at edge
      exact old.component.parents current included parent edge
    children := by
      intro current included child member
      rw [topology_node] at member
      exact old.component.children current included child member }
  refine ⟨⟨component,?_⟩,rfl⟩
  intro kind position included bound
  by_cases fresh : position = slot.index.toNat
  · subst position
    refine ⟨⟨.ReservedFrz false,false,.None⟩,?_,?_⟩
    · rw [projection_location_state (slot.after tag) location protections slot.index
        (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)
        (GeneralBorrowFreshLocation.get_same tree.nodes slot.index _)]
      simp only [BorrowTree.locationStateAt,show (slot.after tag).nodeAt slot.index = some
          (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None) from GeneralBorrowFreshLocation.get_same _ _ _,clean]
      rfl
    · rw [foreign_new tree slot tag depth location protections observer node present]
      exact reserved_foreign kind _
  · have oldBound := old_bound tree slot tag position bound fresh
    obtain ⟨query,converted,equal⟩ := index_nat position (by omega)
    have different : query ≠ slot.index := by
      intro same
      exact fresh (equal.symm.trans (congrArg UniIndex.toNat same))
    obtain ⟨state,lookup,compatible⟩ := old.permissions kind position included oldBound
    have oldState : (source_normal_projection (slot.after tag) location protections).stateAt position =
        (source_normal_projection tree location protections).stateAt position := by
      rw [projection_slot _ _ _ position query converted equal bound,
        projection_slot _ _ _ position query converted equal oldBound]
      have lookup : (slot.after tag).nodeAt query = tree.nodeAt query :=
        GeneralBorrowFreshLocation.get_other tree.nodes slot.index query _ different
      rw [lookup]
    refine ⟨state,oldState.trans lookup,?_⟩
    have held := protected_old tree slot tag location protections query different
    rw [equal] at held
    rw [held]
    unfold GeneralBorrowAnchor.relation
    rw [old_path tree slot tag depth location protections observer node present]
    exact compatible

end DuplicatePrefix.S04ZeroRootObserverNormal
