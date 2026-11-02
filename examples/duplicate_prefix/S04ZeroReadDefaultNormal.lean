import duplicate_prefix.S04ZeroReadDefaultEntry
import duplicate_prefix.GeneralBorrowObserverSharedExtension

namespace DuplicatePrefix.S04ZeroReadDefaultNormal
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowPresence GeneralBorrowFreshNormalComponent
open GeneralBorrowFreshNode GeneralBorrowNodeUpdate
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

/-- A vacant index is removed before the actual new leaf is added, and the
leaf belongs precisely when its constructor parent belongs. -/
def support (old : Nat → Prop) (parent child : Nat) : Nat → Prop :=
  fun index => (old index ∧ index ≠ child) ∨ (index = child ∧ old parent)

private theorem parent_of_child (tree : TraversalTree) (forest : GeneralBorrowForest.Forest tree)
    (current query : Nat) (member : query ∈ (nodeData tree current).children) :
    (nodeData tree query).parent = some current := by
  by_cases valid : current < tree.nodes.size
  · have raw : query ∈ tree.nodes[current].children := by
      simpa only [nodeData,Array.getElem?_eq_getElem valid,Option.getD_some] using member
    obtain ⟨bounded,edge⟩ := forest.childParent current valid query raw
    simpa only [nodeData,Array.getElem?_eq_getElem bounded,Option.getD_some] using edge
  · simp only [nodeData,Array.getElem?_eq_none (Nat.le_of_not_gt valid),Option.getD_none] at member
    cases member

private theorem no_parent_leaf (tree : TraversalTree) (forest : GeneralBorrowForest.Forest tree)
    (child : Nat) (leaf : (nodeData tree child).children = []) (current : Nat) :
    (nodeData tree current).parent ≠ some child := by
  intro edge
  by_cases valid : current < tree.nodes.size
  · have raw : tree.nodes[current].parent = some child := by
      simpa only [nodeData,Array.getElem?_eq_getElem valid,Option.getD_some] using edge
    obtain ⟨bounded,member⟩ := forest.parentChild current valid child raw
    have empty : tree.nodes[child].children = [] := by
      simpa only [nodeData,Array.getElem?_eq_getElem bounded,Option.getD_some] using leaf
    rw [empty] at member
    cases member
  · simp only [nodeData,Array.getElem?_eq_none (Nat.le_of_not_gt valid),Option.getD_none] at edge
    cases edge

/-- Exact component transport for an arbitrary old observer, whether or not
the constructor parent lies in its component. -/
def component (before after : TraversalTree) (parent child observer : Nat)
    (old : GeneralBorrowExposedScopedNormal.Component before observer)
    (different : observer ≠ child) (patch : Patch before after parent child)
    (forest : GeneralBorrowForest.Forest after) :
    GeneralBorrowExposedScopedNormal.Component after observer where
  support := support old.support parent child
  anchor := .inl ⟨old.anchor,different⟩
  parents := by
    intro current included parentNode edge
    by_cases fresh : current = child
    · subst current
      have parentSupported := (included.resolve_left (by simp)).2
      rw [patch.leaf] at edge
      have same : parent = parentNode := Option.some.inj edge
      subst parentNode
      exact .inl ⟨parentSupported,by
        intro same
        subst parent
        exact no_parent_leaf after forest child (congrArg TraversalNode.children patch.leaf)
          child (congrArg TraversalNode.parent patch.leaf)⟩
    · have previous := (included.resolve_right (by simp [fresh])).1
      refine .inl ⟨old.parents current previous parentNode
        ((patch.oldParents current fresh).symm.trans edge),?_⟩
      intro same
      subst parentNode
      exact no_parent_leaf after forest child (congrArg TraversalNode.children patch.leaf) current edge
  children := by
    intro current included query member
    by_cases fresh : current = child
    · subst current
      rw [patch.leaf] at member
      cases member
    · have previous := (included.resolve_right (by simp [fresh])).1
      by_cases newChild : query = child
      · subst query
        have edge := parent_of_child after forest current child member
        rw [patch.leaf] at edge
        have same : parent = current := Option.some.inj edge
        exact .inr ⟨rfl,same ▸ previous⟩
      · exact .inl ⟨old.children current previous query
          ((patch.oldChildren current fresh query member).resolve_left newChild),newChild⟩

private theorem size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection; unfold_general_topology; simp only [Array.size_map]

/-- The allocator-selected append/reuse supplies the complete actual stage
attachment, including production ancestor-path fuel and old-index bounds. -/
theorem topology (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadDefaultEntry.Input tree parentTag tag)
    (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology) :
    ∃ _nextForest : GeneralBorrowForest.Forest (source_normal_projection input.stage location protections).topology,
      Patch (source_normal_projection tree location protections).topology
        (source_normal_projection input.stage location protections).topology input.parent.toNat input.index.toNat ∧
      GeneralBorrowFreshSharedPaths.Attach (source_normal_projection tree location protections).topology
        (source_normal_projection input.stage location protections).topology input.parent.toNat input.index.toNat ∧
      (∀ index,index < input.stage.nodes.data.size → index ≠ input.index.toNat → index < tree.nodes.data.size) := by
  cases selected : input.slot with
  | append noFree aligned fits =>
    have atEnd : input.index.toNat = tree.nodes.data.size := by
      simp only [S04ZeroReadDefaultEntry.Input.index,selected,GeneralBorrowFreshMetadataChildSlot.index,
        UniIndex.toNat,UInt32.toNat_ofNat',Nat.mod_eq_of_lt (by omega : tree.tagMapping.mapping.size < 2^32)]
      exact aligned
    have ext := GeneralBorrowFreshProjection.topology_extension tree input.index input.parent input.parentNode
      (GeneralBorrowFreshDefaultChild.child tag input.parent) atEnd input.present rfl rfl location location protections
    change GeneralBorrowFreshTopology.Extension (source_normal_projection tree location protections).topology
      (source_normal_projection input.stage location protections).topology input.parent.toNat at ext
    have patch := GeneralBorrowFreshNormalComponent.of_append _ _ _ ext
    have paths := GeneralBorrowFreshSharedPaths.of_append _ _ _ ext forest
    rw [size,←atEnd] at patch paths
    refine ⟨GeneralBorrowFreshTopology.extended_forest _ _ _ ext forest,patch,paths,?_⟩
    have length := ext.length
    rw [size,size] at length
    intro index bound different
    omega
  | reuse child available bounded missing slack =>
    have indexEq : input.index = child := by simp only [S04ZeroReadDefaultEntry.Input.index,selected,GeneralBorrowFreshMetadataChildSlot.index]
    have ext := GeneralBorrowFreshReuseProjection.topology_extension tree input.index input.parent input.parentNode
      (GeneralBorrowFreshDefaultChild.child tag input.parent) (by rw [indexEq];exact bounded) input.vacant input.present
      rfl rfl location location protections
    change GeneralBorrowFreshReuseTopology.Extension (source_normal_projection tree location protections).topology
      (source_normal_projection input.stage location protections).topology input.index.toNat input.parent.toNat at ext
    refine ⟨GeneralBorrowFreshReuseTopology.extended_forest _ _ _ _ ext forest,
      GeneralBorrowFreshNormalComponent.of_reuse _ _ _ _ ext,
      GeneralBorrowFreshSharedPaths.of_reuse _ _ _ _ ext forest,?_⟩
    have length := ext.length
    rw [size,size] at length
    intro index bound different
    omega

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


private theorem stage_default (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadDefaultEntry.Input tree parentTag tag) (query : UniIndex)
    (different : query ≠ input.index) :
    ((input.stage.nodeAt query).map TreeNode.defaultLocationState).getD absentDefault =
      ((tree.nodeAt query).map TreeNode.defaultLocationState).getD absentDefault := by
  have parentDifferent := GeneralBorrowFreshReuseNode.parent_not_vacant tree.nodes input.index input.parent
    input.parentNode input.vacant input.present
  have old := (GeneralBorrowFreshLocation.get_other tree.nodes input.index input.parent
    (GeneralBorrowFreshDefaultChild.child tag input.parent) parentDifferent).trans input.present
  change ((((tree.nodes.insert input.index (GeneralBorrowFreshDefaultChild.child tag input.parent)).insert
    input.parent {input.parentNode with children := input.parentNode.children.push input.index}).get query).map
      TreeNode.defaultLocationState).getD absentDefault = _
  by_cases same : query = input.parent
  · subst query
    rw [insert_existing_get_same _ input.parent input.parentNode _ old,input.present]
    rfl
  · rw [insert_existing_get_other _ input.parent query input.parentNode _ old same,
      GeneralBorrowFreshLocation.get_other tree.nodes input.index query _ different]
    rfl

private theorem stage_state_old (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadDefaultEntry.Input tree parentTag tag)
    (location : LocationTree) (protections : ProtectedTags) (fits : tree.nodes.data.size ≤ 4294967296)
    (position : Nat) (valid : position < tree.nodes.data.size)
    (afterValid : position < input.stage.nodes.data.size) (different : position ≠ input.index.toNat) :
    (source_normal_projection input.stage location protections).stateAt position =
      (source_normal_projection tree location protections).stateAt position := by
  obtain ⟨query,converted,equal⟩ := index_nat position (by omega)
  have queryDifferent : query ≠ input.index := by
    intro same
    exact different (equal.symm.trans (congrArg UniIndex.toNat same))
  rw [projection_slot _ _ _ position query converted equal afterValid,
    projection_slot tree location protections position query converted equal valid,
    stage_default tree parentTag tag input query queryDifferent]

private theorem reserved_foreign (kind : AccessKind) (held : Bool) :
    DuplicatePrefixScalarAuthorization.Compatible ⟨.ReservedFrz false,false,.Read⟩ kind .ForeignAccess held := by
  cases kind <;> cases held <;>
    simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
      GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]

/-- The actual zero-size attachment preserves every old observer's normal
Read/Write authorization, even in a different component. The new zero-extent
leaf is inactive and foreign to every old source. -/
theorem stage (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadDefaultEntry.Input tree parentTag tag)
    (location : LocationTree) (protections : ProtectedTags)
    (fits : tree.nodes.data.size ≤ 4294967296)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (clean : location.perms.get input.index = none)
    (observer : UniIndex) (observerNode : TreeNode) (present : tree.nodeAt observer = some observerNode)
    (old : DuplicatePrefixBorrowAuthorization.Normal tree location protections observer) :
    ∃ next : DuplicatePrefixBorrowAuthorization.Normal input.stage location protections observer,
      next.component.support = support old.component.support input.parent.toNat input.index.toNat ∧
      (source_normal_projection input.stage location protections).topology.ancestorPath observer.toNat =
        (source_normal_projection tree location protections).topology.ancestorPath observer.toNat := by
  have valid := lookup_valid tree.nodes observer observerNode present
  have different : observer.toNat ≠ input.index.toNat := by
    intro same
    have equal : observer = input.index := by
      have injective : Function.Injective UniIndex.toNat := by
        intro a b eq
        cases a; cases b
        exact congrArg UniIndex.mk (UInt32.toNat_inj.mp eq)
      exact injective same
    change tree.nodes.get observer = some observerNode at present
    rw [equal,input.vacant] at present
    cases present
  obtain ⟨afterForest,patch,paths,backward⟩ := topology tree parentTag tag input location protections forest
  let next := component _ _ input.parent.toNat input.index.toNat observer.toNat old.component different patch afterForest
  refine ⟨⟨next,?_⟩,rfl,paths.oldPath observer.toNat (by rw [size];exact valid) different⟩
  intro kind index included bound
  by_cases fresh : index = input.index.toNat
  · subst index
    refine ⟨⟨.ReservedFrz false,false,.Read⟩,?_,?_⟩
    · rw [GeneralBorrowProjection.projection_location_state input.stage location protections
        input.index (GeneralBorrowFreshDefaultChild.child tag input.parent) input.stage_new]
      simp only [BorrowTree.locationStateAt,input.stage_new,clean]
      rfl
    · rw [GeneralBorrowSharedNormalRelations.original_child_foreign _ _ input.parent.toNat input.index.toNat
        observer.toNat paths (by rw [size];exact valid) different]
      exact reserved_foreign kind _
  · have oldBound := backward index bound fresh
    have oldIncluded : old.component.support index := (included.resolve_right (by simp [fresh])).1
    obtain ⟨state,lookup,compatible⟩ := old.permissions kind index oldIncluded oldBound
    refine ⟨state,(stage_state_old tree parentTag tag input location protections fits index oldBound bound fresh).trans lookup,?_⟩
    rw [GeneralBorrowSharedNormalRelations.original _ _ input.parent.toNat input.index.toNat observer.toNat
      index paths (by rw [size];exact valid) different]
    have held := GeneralBorrowFreshReuseProtection.protection_position tree input.index input.parent input.parentNode
      (GeneralBorrowFreshDefaultChild.child tag input.parent) input.vacant input.present location location protections fits
      index oldBound fresh
    change (source_normal_projection input.stage location protections).protectedNodes.contains index =
      (source_normal_projection tree location protections).protectedNodes.contains index at held
    rw [held]
    exact compatible

/-- Each actual old row supplies fresh vacancy from the initial pool packet. -/
theorem at_row (tree : BorrowTree) (parentTag tag : BorTag)
    (input : S04ZeroReadDefaultEntry.Input tree parentTag tag)
    (protections : ProtectedTags) (fits : tree.nodes.data.size ≤ 4294967296)
    (position : Nat) (valid : position < tree.locations.entries.size)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree
      (tree.locations.entries[position]'valid).data protections).topology)
    (observer : UniIndex) (observerNode : TreeNode) (present : tree.nodeAt observer = some observerNode)
    (old : DuplicatePrefixBorrowAuthorization.Normal tree (tree.locations.entries[position]'valid).data protections observer) :
    ∃ next : DuplicatePrefixBorrowAuthorization.Normal input.stage (tree.locations.entries[position]'valid).data protections observer,
      next.component.support = support old.component.support input.parent.toNat input.index.toNat ∧
      (source_normal_projection input.stage (tree.locations.entries[position]'valid).data protections).topology.ancestorPath observer.toNat =
        (source_normal_projection tree (tree.locations.entries[position]'valid).data protections).topology.ancestorPath observer.toNat :=
  stage tree parentTag tag input _ protections fits forest (input.clean position valid) observer observerNode present old

end DuplicatePrefix.S04ZeroReadDefaultNormal
